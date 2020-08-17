#use "Lexer.ml";;

type line = token list

type statement = SimpleStmt of line
               | IfStmt of line * statement * (statement option)
               | WhileStmt of line * statement
               | ForStmt of line * statement
               | BlockStmt of statement list

type func = 
    { name  : string;
      ty    : ty;
      args  : (ty * string) list;
      ast   : statement;
    }

module type PARSER =
  sig
    val split_lines : token list -> func StrMap.t
    val gen_function_pool : token list -> func StrMap.t
  end

module Parser =
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

    (* from a list of tokens, find the first stmt and construct it *)
    let rec stmt_construct : (statement, token) m = fun ts ->
        match ts with
        | If::LParen::xs ->
            runState ts @@
            let+ cond    = get_pair (LParen, RParen) in
            let+ if_stmt = stmt_construct in
            let+ state   = get in 
            (match state with
            | Else::xs' -> 
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
            
    let split_lines (filename : string) : func StrMap.t res = 
        let* (lexed, tdict, tlist, sinfo) = Lexer.lex filename in 
        let* fpool = gen_function_pool lexed in
        Ok fpool
  end


