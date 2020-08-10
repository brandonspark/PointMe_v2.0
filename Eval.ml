#use "Parser.ml";;

type obj = CharObj of char
         | IntObj of int
         | StrObj of string
         | BoolObj of bool
         | StructObj of ty * ((string * obj) list)
         | PtrObj of ty * (obj ref option)
         | ArrObj of ty * (obj Array.t option)

and var = string * ty * obj

type assign = unit 
type state = (line * assign list) list   (* list of previous lines + what they did *)
           * (line * assign list) list   (* list of next lines + what they do *)
           * var StrMap.t                (* map keeping stack data *)
           * obj ref StrMap.t            (* map keeping heap data *)

type tok = Operator of token
         | Obj of obj

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

    (* calc should be able to *)
    let peek (lref : 'a list ref) =
        match !lref with
        | [] -> None 
        | x::xs -> Some x

    let pop (lref : 'a list ref) =
        match !lref with
        | [] -> failwith "Cannot pop on empty list."
        | x::xs -> (lref := xs; x)

    let prefix_bp (t : token) =
        match t with
        | Bang | Tilde | Minus | Asterisk -> 23
        | _ -> failwith "Not a valid prefix token."

    let infix_bp (t : token) =
        match t with
        | LParen | RParen | Arrow | Period -> Some (25, 26)
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

    exception Error of token list 
    exception TokenError of token 
    (* set up the AST, then break it *)
    let rec calc (ts : token list ref) (funcmap : func StrMap.t)
                 ((prev, next, stack, heap) : state) =
        let tokens = ts in
        let prevRef = ref prev in
        let nextRef = ref next in
        let stackRef = ref stack in
        let heapRef = ref heap in

        (* parse the first expression seen *)
        let rec expr_bp (bp : int) =

            (* initially set lhs *)
            let lhs = 
                (let t = pop tokens in 
                  match t with
                | Identifier name -> Name name
                | Const n -> Lit (IntObj n) 
                | StrLit s -> Lit (StrObj s)
                | ChrLit c -> Lit (CharObj c)
                | Bool b -> Lit (BoolObj b)
                | Bang | Tilde | Asterisk | Minus ->
                  let r_bp = prefix_bp t in
                    UnOp (t, expr_bp r_bp)
                | LParen -> let lhs = expr_bp 0 in 
                            (match pop tokens with
                            | RParen -> lhs (* recurse for one expression *)
                            | _ -> failwith "Expected RParen.")
                | _ -> raise (TokenError t)) in
             
            (* define expect *)
            let expect (t : token) = 
                let next = pop tokens in
                (if next = t then ()
                            else failwith "Did not receive expected token.") in

            let rec main (lhs : ast) (bp : int) = 
                let op = (match peek tokens with
                          | None -> raise (Break lhs)
                          | Some o -> o) in
                
                (match postfix_bp op with 
                 | Some l_bp -> if l_bp < bp then raise (Break lhs)
                    else (
                    let _ = pop tokens in
                    let lhs = 
                        (match op with 
                        | LBracket -> 
                            let rhs = expr_bp 0 in
                            let () =  expect RBracket in
                                main (ArrayAccess (lhs, rhs)) bp
                        | LParen -> failwith "Unimplemented"
                            (* do some function stuff here 
                             * basically, call expr_bp until you reach RParen,*
                             * ig *)) in
                        raise (Continue (lhs, bp)))
                 | _ ->
                    (match infix_bp op with
                     | Some (l_bp, r_bp) -> if l_bp < bp then raise (Break lhs)
                        else ( 
                        let _ = pop tokens in
                        let lhs =
                            (match op with
                            | QMark -> let mhs = expr_bp 0 in
                                       let () = expect Colon in
                                       let rhs = expr_bp 0 in
                                       main (Cond (lhs, mhs, rhs)) bp
                            | Period | Arrow -> let rhs = expr_bp r_bp in
                                                let Lit (StrObj name) = rhs in
                                main (if Period = op then (DotAccess (lhs, name))
                                                     else (ArrowAccess (lhs, name))) bp
                            | _ -> let rhs = expr_bp r_bp in
                                main (BinOp (op, lhs, rhs)) bp) in 
                            raise (Continue (lhs, bp)))
                     | _ -> raise (Break lhs))) in
            (try main lhs bp with (Continue (ast, n)) -> main ast n
                                | (Break ast) -> ast) in
        expr_bp 0


    let test (filename : string) = 
        let (tokens, typedict, typelist) = Lexer.lex filename in
        let (prev, next, stack, heap) = ([], [], StrMap.empty, StrMap.empty) in
        calc (ref tokens) (StrMap.empty) (prev, next, stack, heap)

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
