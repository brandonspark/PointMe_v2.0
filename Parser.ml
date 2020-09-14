#use "Lexer.ml";;

type line = token list

type statement = SimpleStmt of line
               | IfStmt of line * statement * (statement option)
               | WhileStmt of line * statement
               | ForStmt of line * statement
               | BlockStmt of statement list
               | ReturnStmt of line
               | AssertStmt of line
               | ErrorStmt of line


type func = 
    { name  : string;
      ty    : ty;
      args  : (ty * string) list;
      ast   : statement;
    }

type obj = CharObj of char
         | IntObj of Int32.t
         | StrObj of string
         | BoolObj of bool
         | VoidObj
         | StructObj of ty * obj StrMap.t
         | PtrObj of ty * ((int * obj ref) option)
         | ArrObj of ty * ((int * obj Array.t) option)

let rec str_obj (o : obj) =
    match o with
    | CharObj c -> Format.sprintf "%c" c
    | StrObj s -> s
    | IntObj n -> Format.sprintf "%d" (Int32.to_int n) 
    | BoolObj b -> if b then "true" else "false"
    | VoidObj -> "<void>"
    | ArrObj (_, None) -> "NULL_ARR"
    | ArrObj (_, Some (i, arr)) ->
        (Printf.sprintf "(%d)" i) ^ Array.fold_right (fun elem acc ->
            ("[" ^ (str_obj elem) ^ "]") ^ acc) arr ""
    | PtrObj (_, None) -> "NULL_PTR"
    | PtrObj (_, Some (i, cell)) -> Printf.sprintf "ptr(%s)" @@ str_obj (!cell)
    | StructObj (_, map) ->
        let init_s = StrMap.fold (fun key obj acc ->
            acc ^ ((Printf.sprintf ", %s: %s") key (str_obj obj)))
            map "{" in
        init_s ^ "}"

module type PARSER =
  sig
    val get_functions : string -> (string * func) list res
    val gen_function_pool : token list -> func StrMap.t res
  end

module Parser : PARSER =
  struct

    open ResultMonad
    open ListStateResMonad

    let rec demarcate_functions : (token list list, token) m = 
        fun ts ->
        match ts with
        | [] -> Ok ([], [])
        | Struct::name::Semicolon::xs -> (* struct foo; *) 
            runState xs @@ 
            eval return_both @@ demarcate_functions
        | Struct::rest -> (* struct foo { type1 x; type2 y; }; *)
            runState rest @@
            let+ _ = get_pair (LCurly, RCurly) in
            let+ _ = expect Semicolon in
            eval return_both @@ demarcate_functions 
        | (Typedef::xs) -> (* typedef type1 type2; *)
            runState xs @@
            let+ _ = find_symbol Semicolon in
            eval return_both @@ demarcate_functions
        | Use::xs -> (* #use <lib> *)
            runState xs @@
            let+ _ = find_symbol RChevron in
            eval return_both @@ demarcate_functions
        | (Type _)::xs -> (* type foo (type1 arg1, type2 arg2){ ... } ; *) 
            runState ts @@
            let+ pre  = get_pair (LParen, RParen) in
            let+ _    = expect LCurly in
            let+ pre' = find_end (LCurly, RCurly) in
            let+ res  = demarcate_functions in
            return_both ((pre @ (LCurly::pre'))::res)
        | x::xs -> Error "Not a valid start to the function."

    let wrapper (t : token) (line : line) =
        match t with
        | Return -> ReturnStmt line
        | Assert -> AssertStmt line
        | Error_t -> ErrorStmt line
        | _ -> failwith "Impossible."

    (* from a list of tokens, find the first stmt and construct it *)
    let rec stmt_construct : (statement, token) m = fun ts ->
        match ts with
        | If::LParen::xs ->
            runState ts @@
            let+ cond    = get_pair (LParen, RParen) in
            let+ if_stmt = stmt_construct in
            let+ next    = peek in 
            (match next with
            | Else -> 
                let+ _         = pop in
                let+ else_stmt = stmt_construct in
                return_both (IfStmt (cond, if_stmt, Some (else_stmt)))
            | _ -> 
                return_both (IfStmt (cond, if_stmt, None)))
        | (For::LParen::xs | While::LParen::xs) ->
            let first::_ = ts in
            runState ts @@
            let+ cond = get_pair (LParen, RParen) in
            let+ stmt = stmt_construct in
            return_both (if first = For then ForStmt (cond, stmt)
                                        else WhileStmt (cond, stmt))
        | ((Return | Assert | Error_t) as t)::xs ->
            runState xs @@
            let+ line = find_symbol Semicolon in
            return_both @@ wrapper t line
        | LCurly::xs -> 
            runState xs @@
            let+ block = find_end (LCurly, RCurly) in
            let+ blocklines = suspend block get_stmts in
            return_both @@ BlockStmt blocklines
        | _ -> 
            runState ts @@
            let+ line = find_symbol Semicolon in
            return_both @@ SimpleStmt line
            
    (* get_stmts is meant to be used to construct the statement list
     * corresponding to the input of all the tokens in a block, given that the token 
     * list does not start with an LCurly. It should also be called on something 
     * terminated with an RCurly. *) 
    and get_stmts : (statement list, token) m =
        fun ts ->
        match ts with
        | [RCurly] -> Ok ([], [])
        | x::xs ->
            runState (x::xs) @@
            let+ stmt1 = stmt_construct in
            let+ stmts = get_stmts in
            return_both (stmt1 :: stmts)
        | _ -> Error "Statements did not end in RCurly."
            
    let rec parse_args (ts : token list) 
                       (acc : (ty * string) list) : (ty * string) list res = 
        match ts with
        | (Type t)::(Identifier id)::Comma::rest -> 
            parse_args rest ((t, id)::acc)
        | (Type t)::(Identifier id)::RParen::rest ->
            Ok (List.rev ((t, id)::acc))
        | _ -> Ok (List.rev acc)
        
    let rec removeStruct (ts : token list) (acc : token list) =
        match ts with
        | [] -> List.rev acc
        | Struct::(Type t)::rest -> removeStruct rest ((Type t)::acc)
        | x::xs -> removeStruct xs (x::acc)
    (* Maps function name to the list of tokens of the function's code. *)
    let rec gen_function_pool (ts : token list) : func StrMap.t res = 
        (* first, demarcate the functions into lists *)
        let* functionLists = runState ts demarcate_functions in
        let noStructLists = List.map (fun l -> removeStruct l []) functionLists in 
        (* next, separate out the name, type, and token list *)
        let nameTypeCode = List.map 
            (function 
            | (Type t)::(Identifier name)::rest as l -> Ok (name, t, l)
            | _ -> Error "function list invalid") noStructLists in
        (* find the statements in each function and return it as a record (result result *)
        let recordMappedResRes = List.map
            (Result.map @@ 
                fun (name, t, l) ->
                runState l @@
                let+ _       = drop 3 in
                let+ arglist = find_symbol LCurly in
                let+ lines   = get_stmts in
                opt_bind (parse_args arglist []) (fun argres ->
                return {name = name; ty = t; args = argres; ast = BlockStmt lines}))
            nameTypeCode in
        (* flatten the result result list into just a result list *)
        let recordMappedRes = List.map
            (function Ok x -> x | Error e -> Error e) recordMappedResRes in
        (* fold over each record result in the list to add it to a dictionary *)
        let foldedRecords = List.fold_left (
            fun res_dict func -> 
            match (func, res_dict) with
            | (Ok ({name = name} as reco), Ok dict) ->
                Ok (StrMap.add name reco dict)
            | _ -> Error "Error in folding.") (Ok StrMap.empty) recordMappedRes in
            foldedRecords
            
    let get_functions (filename : string) = 
        let* (lexed, tdict, tlist, sinfo) = Lexer.lex filename in 
        let* fpool = gen_function_pool lexed in
        Ok (Utils.dict_to_list fpool)
  end

module type PRATT =
  sig
    type ast
    val expr_bp : int -> (ast, token) ListStateResMonad.m
    val str_pratt : ast -> string
    val test : string -> ast res
  end

module Pratt =
  struct
    open ListStateResMonad

    type ast = BinOp of token * ast * ast
             | UnOp of token * ast
             | Call of string * ast list
             | Name of string
             | Lit of obj
             | DotAccess of ast * string
             | ArrowAccess of ast * string
             | ArrayAccess of ast * ast
             | Cond of ast * ast * ast
             | AllocNode of ty
             | AllocArrNode of ty * ast

    let rec str_ast (a : ast) =
        match a with
        | BinOp (t, l, r) -> Printf.sprintf "BinOp (%s, %s, %s)" (str_token t)
                             (str_ast l) (str_ast r)
        | UnOp (t, x) -> Printf.sprintf "UnOp (%s, %s)" (str_token t) (str_ast x)
        | Call (name, l) ->
            "(" ^ (List.fold_right (fun elem acc ->
                (str_ast elem) ^ acc) l ")")
        | Name n -> n
        | Lit o -> str_obj o
        | DotAccess (x, f) -> Printf.sprintf "%s.%s" (str_ast x) f
        | ArrowAccess (x, f) -> Printf.sprintf "%s->%s" (str_ast x) f
        | ArrayAccess (x, y) -> Printf.sprintf "%s[%s]" (str_ast x) (str_ast y)
        | Cond (i, t, e) -> Printf.sprintf "%s ? %s : %s" (str_ast i) (str_ast
        t) (str_ast e)
        | AllocNode t -> Printf.sprintf "alloc(%s)" (str_ty t)
        | AllocArrNode (t, x) -> Printf.sprintf "alloc_array(%s, %s)" (str_ty t) (str_ast x)

    let prefix_bp (t : token) =
        match t with
        | Bang | Tilde | Minus | Asterisk -> 23
        | _ -> failwith "Not a valid prefix token."

    let infix_bp (t : token) =
        match t with
        | Arrow | Period -> Some (25, 26)
        | Asterisk | Slash | Percent -> Some (21, 22)
        | Plus | Minus -> Some (19, 20)
        | LShift | RShift -> Some (17, 18)
        | LChevron | Leq | Geq | RChevron -> Some (15, 16)
        | EqEq | NotEq -> Some (13, 14)
        | Amper -> Some (11, 12)
        | Caret -> Some (9, 10)
        | Pipe -> Some (7, 8)
        | And -> Some (5, 6)
        | Or -> Some (3, 4)
        | QMark -> Some (1, 2)
        | _ -> None
        

    let postfix_bp (t : token) =
        match t with
        | LParen | LBracket -> Some 27
        | _ -> None

    exception InvalidToken of token list 

    let expectID : (string, token) m =
        fun ts ->
        runState ts @@
        let+ state = get in
        match state with
        | (Identifier name)::rest -> return (name, rest)
        | _ -> return_err "Did not get an identifier next."

    exception InvalidAST of ast

    let rec get_args_list (acc : ast list) : (ast list, token) m =
        fun ts ->
        match ts with
        | [RParen] -> Ok (List.rev acc, [])
        | [Comma] -> Error "Function args ends in semicolon."
        | Comma::xs ->
            runState xs @@
            eval return_both @@ get_args_list acc
        | x::xs ->
            runState (x::xs) @@
            let+ ast = expr_bp 0 in
            eval return_both @@ get_args_list (ast::acc)
            (*eval return_both @@ get_args_list (ast::acc)*)
        | _ -> Error "Did not find an RParen at the end of function call."   

    (* nud, given a token list, returns Ok (lhs, rest), where
     * lhs is the first standalone expression found with no left-context,
     * and rest is the rest of the tokens that follow it *)
    and nud : (ast, token) m =
        fun ts ->
        runState ts @@
        let+ t = pop in 
        match t with
        | Identifier name -> return_both @@ Name name
        | Const n -> return_both @@ Lit (IntObj n)
        | StrLit s -> return_both @@ Lit (StrObj s) 
        | ChrLit c -> return_both @@ Lit (CharObj c)
        | Bool b -> return_both @@ Lit (BoolObj b)
        | Bang | Tilde | Asterisk | Minus ->
            let r_bp = prefix_bp t in
            let+ hs  = expr_bp r_bp in
            return_both @@ UnOp (t, hs)
        | LParen -> 
            let+ lhs = expr_bp 0 in 
            let+ _   = expect RParen in
            return_both lhs (* recurse for one expression *)
        | Alloc ->
            let+ _     = expect LParen in
            let+ next  = pop in
            let+ _     = expect RParen in
            (match next with
            | Type t -> return_both @@ AllocNode t
            | _ -> return_err "Alloc was not passed a type.")
        | Alloc_array ->
            let+ _   = expect LParen in
            let+ t   = pop in
            let+ _   = expect Comma in
            let+ num = expr_bp 0 in
            let+ _   = expect RParen in
            (match t with
            | Type t -> return_both @@ AllocArrNode (t, num)
            | _ -> return_err "Alloc_array was not passed a type.")
        | _ -> return_err "No tokens left"

    (* led, given an AST, binding power, and token list, searches the token
     * list, constructing an AST according to the left context of the LHS,
     * until it runs out. If it reaches something with a higher binding
     * power, it backtracks. *)
    and led (lhs : ast) (bp: int) : (ast, token) m =
        fun ts ->
        runState ts @@
        let+ state = get in
        match state with
        | [] -> return_both lhs
        | op::_ -> 
            (match (postfix_bp op, infix_bp op) with 
            (**********************
             * POSTFIX OPERATORS  *
             **********************)
            | (Some l_bp, _) -> 
                if l_bp < bp then return_both lhs
                else
                    let+ _       = pop in 
                    (match op with 
                    (* Array Indexing: e.g. var[10] *)
                    | LBracket -> 
                        let+ rhs     = expr_bp 0 in
                        let+ _       = expect RBracket in
                        let+ new_lhs = led (ArrayAccess (lhs, rhs)) bp in
                        eval return_both @@ led new_lhs bp
                    (* Function Calls: e.g. f(x, y, z) *)
                    | LParen -> 
                        (match lhs with
                        | Name name ->
                            let+ arglist = find_end (LParen, RParen) in
                            let _ = Utils.print_blue "before args\n" in
                            let+ args    = suspend arglist @@ get_args_list [] in
                            let _ = Utils.print_blue "done with args\n" in
                            let+ new_lhs = led (Call (name, args)) bp in 
                            eval return_both @@ led new_lhs bp
                        | _ -> return_err "LParen found after non-name")
                    (* Every other postfix - shouldn't exist. *)
                    | _ -> return_both lhs (* "shouldn't error here, only two
                    postfix" *))
            (**********************
             * INFIX OPERATORS    *
             **********************)
            | (None, Some (l_bp, r_bp)) ->
                if l_bp < bp then return_both lhs
                else
                    let+ _ = pop in 
                    (match op with
                    (* Conditionals: e.g. x ? y : z *)
                    | QMark -> 
                        let+ mhs = expr_bp 0 in
                        let+ _   = expect Colon in
                        let+ rhs = expr_bp 0 in
                        let+ new_lhs = led (Cond (lhs, mhs, rhs)) bp in
                        eval return_both @@ led new_lhs bp
                    (* Field Derefences: e.g. var.field or var->field *)
                    | Period | Arrow ->
                        let+ name = expectID in
                        eval return_both @@
                        led (if Period = op then (DotAccess (lhs, name))
                                            else (ArrowAccess (lhs, name))) bp
                    (* Every other infix operator is a BinOp *)
                    | _ -> 
                        let+ rhs = expr_bp r_bp in 
                        eval return_both @@ led (BinOp (op, lhs, rhs)) bp)
            | _ -> return_both lhs)
    
    (* parse the first expression seen *)
    and expr_bp (bp : int) : (ast, token) m =
        fun ts ->
        runState ts @@ 
        let+ lhs = nud in
        eval return_both @@ led lhs bp

    let rec str_pratt (a : ast) =
        match a with
        | BinOp (t, a1, a2) -> Format.sprintf "(%s %s %s)" (str_pratt a1)
                                              (str_token t) (str_pratt a2)
        | UnOp (t, a1) -> Format.sprintf "(%s %s)" (str_token t) (str_pratt a1)
        | Call (s, l) -> 
            Format.sprintf "%s(%s)" s
                (let interior = 
                    (List.fold_right (fun a1 acc -> 
                    Format.sprintf "%s, %s" (str_pratt a1) acc) l "") in
                String.sub interior 0 (String.length interior - 2))
        | Name n -> Format.sprintf "\"%s\"" n
        | Lit l -> str_obj l
        | DotAccess (a1, s) -> Format.sprintf "%s.%s" (str_pratt a1) s
        | ArrowAccess (a1, s) -> Format.sprintf "%s->%s" (str_pratt a1) s
        | ArrayAccess (a1, a2) -> Format.sprintf "%s[%s]" (str_pratt a1) (str_pratt a2)
        | Cond (c, a1, a2) -> Format.sprintf "(%s ? %s : %s)" (str_pratt c)
                                             (str_pratt a1) (str_pratt a2) 
        | AllocNode t -> Format.sprintf "alloc(%s)" (str_ty t)
        | AllocArrNode (t, ast) -> Format.sprintf "alloc_array(%s, %s)"
                                   (str_ty t) (str_pratt ast)
    open ResultMonad

    let test (filename : string) = 
        let* (tokens, typedict, typelist, sinfo) = Lexer.lex filename in
        let* ast = runState tokens @@ expr_bp 0 in
        let () = Utils.print_blue (str_pratt ast) in 
        let () = print_string "\n" in
        Ok ast
  end
