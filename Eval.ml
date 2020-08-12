#use "Parser.ml";;

type obj = CharObj of char
         | IntObj of int
         | StrObj of string
         | BoolObj of bool
         | StructObj of ty * ((string * obj) list)
         | PtrObj of ty * (obj ref option)
         | ArrObj of ty * (obj Array.t option)

let str_obj (o : obj) =
    match o with
    | CharObj c -> Format.sprintf "%c" c
    | StrObj s -> s
    | IntObj n -> Format.sprintf "%d" n 
    | BoolObj b -> if b then "true" else "false"
    | _ -> "[NOT SUPPORTED]"

type var = string * ty * obj

type assign = unit 
type state = (line * assign list) list   (* list of previous lines + what they did *)
           * (line * assign list) list   (* list of next lines + what they do *)
           * var StrMap.t                (* map keeping stack data *)
           * obj ref StrMap.t            (* map keeping heap data *)


module Pratt =
  struct
    type ast = BinOp of token * ast * ast
             | UnOp of token * ast
             | Call of string * ast list
             | Name of string
             | Lit of obj
             | DotAccess of ast * string
             | ArrowAccess of ast * string
             | ArrayAccess of ast * ast
             | Cond of ast * ast * ast

    let prefix_bp (t : token) =
        match t with
        | Bang | Tilde | Minus | Asterisk -> 23
        | _ -> failwith "Not a valid prefix token."

    let infix_bp (t : token) =
        match t with
        | LParen | Arrow | Period -> Some (25, 26)
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
        | Increment | Decrement -> Some 23
        | _ -> None

    exception Break of ast 
    exception Continue of ast * int
    let infix = [Arrow; Period; Asterisk; Slash; Percent; Plus; Minus; LShift; RShift;
                 LChevron; Leq; Geq; RChevron; EqEq; NotEq; Amper; Caret; Pipe;
                 And; Or; QMark; Colon]

    let postfix = [LParen; LBracket]

    (* set up the AST, then break it *)
    let pop (ts : token list) : (token * token list) res =
        match ts with
        | x::xs -> Ok (x, xs)
        | _ -> Error "Cannot pop from empty list."
    
    let peek (ts : token list) : token res =
        match ts with
        | x::xs -> Ok x
        | _ -> Error "Cannot peek from empty list."

    let expect (t : token) (ts : token list) : token list res = 
        let* (res, rest) = pop ts in
        if res = t then Ok rest
                   else Error "Not what was expected"

    let expectID (ts : token list) : (string * token list) res =
        match pop ts with
        | Ok (Identifier name, rest) -> Ok (name, rest)
        | Error e -> Error "Did not get an identifier next."

    let rec get_args_list (ts : token list) (acc : ast list) : ast list res =
        match ts with
        | [RParen] -> Ok (List.rev acc)
        | x::xs -> 
            let* (ast, after_ts) = expr_bp 0 ts in
            get_args_list after_ts (ast::acc)
        | _ -> Error "Did not find an RParen at the end of function call."

    

    (* nud, given a token list, returns Ok (lhs, rest), where
     * lhs is the first standalone expression found with no left-context,
     * and rest is the rest of the tokens that follow it *)
    and nud (ts : token list) : (ast * token list) res =
        let* (t, rest) = pop ts in 
        match t with
        | Identifier name -> 
            (*let* (t, after_ts) = pop ts in
            (match t with
            | LParen -> 
                let* (pre, post) = Utils.find_end after_ts (LParen, RParen) in
                let* args = get_args_list pre [] in
                Ok (Call (name, args), post)
            | _ -> *)Ok (Name name, rest)
        | Const n -> Ok (Lit (IntObj n), rest)
        | StrLit s -> Ok (Lit (StrObj s), rest) 
        | ChrLit c -> Ok (Lit (CharObj c), rest)
        | Bool b -> Ok (Lit (BoolObj b), rest)
        | Bang | Tilde | Asterisk | Minus ->
            let r_bp = prefix_bp t in
            let* (hs, rest_ts) = expr_bp r_bp rest in
            Ok (UnOp (t, hs), rest_ts)
        | LParen -> 
            let* (lhs, rest') = expr_bp 0 rest in 
            let* final_ts = expect RParen rest' in
            Ok (lhs, final_ts) (* recurse for one expression *)
        | _ -> Error "No tokens left"

    (* led, given an AST, binding power, and token list, searches the token
     * list, constructing an AST according to the left context of the LHS,
     * until it runs out. If it reaches something with a higher binding
     * power, it backtracks. *)
    and led (lhs : ast) (bp: int) (ts : token list) : (ast * token list) res =
        match pop ts with
        | Error _ -> Ok (lhs, ts)
        | Ok (op, init_ts) -> 
            (match (postfix_bp op, infix_bp op) with 
            | (Some l_bp, _) -> (* for postfix operators *)
                if l_bp < bp then Ok (lhs, ts) (* precedence, return what we have *)
                else
                    let* (new_lhs, final_ts) = 
                    (match op with 
                    | LBracket ->
                        let* (rhs, rhs_ts) = expr_bp 0 init_ts in
                        let* expected_ts = expect RBracket rhs_ts in
                        led (ArrayAccess (lhs, rhs)) bp expected_ts
                    | LParen -> 
                        (match lhs with
                        | Name name ->
                            let* (pre, post) = Utils.find_end init_ts (LParen, RParen) in
                            let* args = get_args_list pre [] in
                            led (Call (name, args)) bp post 
                        | _ -> Error "LParen found after non-name")
                    | _ -> Error "shouldn't error here, only two postfix"
                    (* do some function stuff here 
                     * basically, call expr_bp until you reach RParen,*
                     * ig *)) in
                    led new_lhs bp final_ts
            | (None, Some (l_bp, r_bp)) ->
                if l_bp < bp then Ok (lhs, ts)
                else
                    (match op with
                    | QMark -> (* x ? y : z *)
                        let* (mhs, mhs_ts)  = expr_bp 0 init_ts in
                        let* expected_ts = expect Colon mhs_ts in
                        let* (rhs, rhs_ts) = expr_bp 0 expected_ts in
                        led (Cond (lhs, mhs, rhs)) bp rhs_ts
                    | Period | Arrow -> (* x.field, x->field *)
                        let* (name, after_ts) = expectID init_ts in
                        led (if Period = op then (DotAccess (lhs, name))
                                             else (ArrowAccess (lhs, name))) bp after_ts
                    | _ -> 
                        let* (rhs, final_ts) = expr_bp r_bp init_ts in 
                        led (BinOp (op, lhs, rhs)) bp final_ts)
            | _ -> Ok (lhs, ts))
    
    (* parse the first expression seen *)
    and expr_bp (bp : int) (ts : token list) : (ast * token list) res =
        (* initially set lhs *)
        let* (lhs, ts1) = nud ts in 
        led lhs bp ts1

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
    let test (filename : string) = 
        let* (tokens, typedict, typelist) = Lexer.lex filename in
        let (prev, next, stack, heap) = ([], [], StrMap.empty, StrMap.empty) in
        let* (a, rest) = expr_bp 0 tokens in
        let () = Utils.print_blue (str_pratt a) in 
        let () = print_string "\n" in
        Ok (a, rest)

    (*type lval = VID of var
              | Field of lval * string
              | Deref of lval
              | Arrow of lval * string
              | Index of lval * ast
    *)

  end

(*module Eval = 
  struct
    
    let rec init_var (t_obj : ty) (name : string) (rest : line) 
                     ((prev, next, stack, heap) : state) =
        match t_obj with
            Base t -> 
          | Ptr t ->
          | Array t -> match line with
                         [Semicolon] -> StrMap.add name (name, t_obj, ArrObj None) 
                         (Equal asn)::rest' -> 

    let rec apply (operator : token) (first : obj) (second : obj) = match token with
        

    (* input the reversed queue - it is now a stack *)
    let rec rpn_eval (ts : tok list) (acc : tok list) = match ts with
        (Operator o)::xs -> let (second, first) = Utils.take_two acc in
            
      | 


    let rec eval_function (funcname: string) (args : var list) (funcmap : func StrMap.t)
                          ((prev, next, stack, heap): state) =
        let ast = StrMap.find funcname funcmap in

        (* eval arguments *) 
        let stack = List.fold_left (fun s (name, t, obj) -> 
            StrMap.add name (name, t, obj) s) stack args in

        (* find the first syntactic expression. *)
        let rec find_exp (line : line) 
                         (sc : line * line -> 'a) 
                         (fc : unit -> 'a) : 'a = 
          match line with
            LParen::rest -> Utils.find_pair line (RParen, LParen) (fun (pre, post) -> 
                sc (pre, post)) fc
          | (Const n)::xs | (StrLit s)::xs | (ChrLit c)::xs | (Bool b)::xs |
            NULL::xs -> let first::rest = line in sc ([first], rest)
          | Bang::xs | Tilde::xs | Asterisk::xs -> let first::rest = line in
                find_exp rest (fun (exp, post) -> sc (first::exp, post)) fc
          | (Identifier name)::LParen::xs ->
                  Utils.find_pair xs (RParen, LParen) (fun (pre, post) ->
                      sc ((Identifier name)::LParen::pre, post)) fc
          | [Alloc; LParen; Type t; RParen] -> sc (line, [])
          | Alloc_array::LParen::xs ->
                  Utils.find_pair xs (RParen, LParen) (fun (pre, post) ->
                      sc (Alloc_array::LParen::pre, post)) fc
          | (Identifier name)::xs -> sc ([Identifier name], xs)
          | 

        let rec eval_expression (line : line) ((prev, next, stack, heap) as v_state : state)
                                (s : tok list) (q : tok list)
                                (sc : line * state * tok list * tok list -> 'a) =
            match line with  
                (StrLit str)::xs ->
                    shunting_yard xs s ((Obj (StrObj s))::q) v_state
              | (ChrLit c)::xs ->
                    shunting_yard xs s ((Obj (ChrObj c))::q) v_state
              | (Const n)::xs ->
                    shunting_yard xs s ((Obj (IntObj n))::q) v_state 
              | (Bool b)::xs ->
                    shunting_yard xs s ((Obj (BoolObj b))::q) v_state
              | (NULL)::xs -> 
                    shunting_yard xs s (Obj (PtrObj (Ptr (Base "void"), None))) v_state
              | (Bang::rest) | (Tilde::rest) | (Asterisk::rest) -> 

              | [Alloc; LParen; Type t; RParen] -> 
              | Alloc_array::LParen::rest -> 
              | (Identifier name)::LParen::xs -> (* function call *)
                      

        let rec eval_statement (ast : statement)
                               ((prev, next, stack, heap) : state) = match ast with
            SimpleStmt line ->

          | IfStmt (cond, code, el) ->
          | WhileStmt (cond, code) ->
          | ForStmt (line, code) ->
          | BlockStmt l ->

        let rec eval_line (line : line) ((prev, next, stack, heap) : state) = match line with 
            (Type ty)::(Identifier name)::rest ->

    let rec eval_program (filename: string) : int =
        let (tokens, tdict, tlist) = Lexer.lex filename in
        let fpool = Parser.gen_function_pool tokens in



  end*)
