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
    
    let fail () = failwith "Failure."

    let rec find_symbol (l : 'a list) (target : 'a) (acc : 'a list)
                        (sc : 'a list * 'a list -> 'b) (fc : unit -> 'b) = match l with
            [] -> fc ()
          | x::xs -> if x = target then sc (List.rev (x::acc), xs)
                                   else find_symbol xs target (x::acc) sc fc

    let rec rd_gdecl (ts : token list) 
                     (sc : token list list -> 'a) 
                     (fc : unit -> 'a) = match ts with
        [] -> sc []
      | (Struct::xs | (Type _)::xs) -> 
                    find_symbol ts Semicolon [] (fun (pre, post) -> 
                        rd_gdecl post (fun res -> sc (pre::res)) fail) fail
      | (Use::xs) -> find_symbol ts RChevron [] (fun (pre, post) ->
                        rd_gdecl post (fun res -> sc (pre::res)) fail) fail
      | _ -> fc ()
    
    (*let rec rd_gdefn (ts : token list)
                     (sc : token list list -> 'a)
                     (fc : unit -> 'a) = match ts with
        [] -> sc []
      | Struct::xs -> find_symbol ts Semicolon [] (fun (pre, post) ->
                        rd_gdefn post (fun res -> sc (pre::res)) fail) fail 
      | *)

    exception InvalidParse of token list

    let rec demarcate_functions (ts : token list)
                                (sc : token list list -> 'a)
                                (fc : unit -> 'a) : 'a = match ts with
        [] -> sc []
      | Struct::name::Semicolon::xs -> demarcate_functions xs sc fc
      | Struct::rest -> find_symbol ts LCurly []
                (fun (_, post) ->
                    Utils.find_pair post (RCurly, LCurly)
                    (fun (_, post') -> match post' with
                        Semicolon::rest -> demarcate_functions rest sc fc
                      | _ -> failwith "No semicolon after struct decl.") fc) fc
      | (Typedef::xs) -> 
              find_symbol ts Semicolon [] (fun (_, post) -> demarcate_functions post sc fail) fail
      | Use::xs -> find_symbol ts RChevron [] (fun (_, post) -> demarcate_functions post sc fail) fail
      | (Type _)::xs -> find_symbol ts RParen []
                (fun (pre, post) -> match post with
                    Semicolon::rest -> demarcate_functions rest sc fc
                  | LCurly::rest -> Utils.find_pair rest (RCurly, LCurly)
                    (fun (pre', post') ->
                        demarcate_functions post' (fun res -> sc ((pre @ LCurly::pre')::res)) fc)
                    (fun () -> failwith "No right curly found.")
                  | _ -> failwith "No semicolon or lcurly after rparen.") fc
      | x::xs -> raise (InvalidParse (x::xs))

    (* get a list of all the token lines from a single statement *)
    let rec stmt_lines (ts : token list)
                       (sc : token list list * token list -> 'b)
                       (fc : unit -> 'b) : 'b = match ts with
        If::LParen::xs -> Utils.find_pair xs (RParen, LParen) 
            (fun (pre, post) -> stmt_lines post (fun (lines, rest) ->
                match rest with
                    Else::xs' -> stmt_lines xs' (fun (lines', rest') ->
                        sc ((If::LParen::pre) :: (lines @ ([Else] :: lines')), rest')) fc
                  | _ -> sc ((If::LParen::pre) :: lines, rest)) fc) fc
      | (For::LParen::xs | While::LParen::xs) -> 
            let first::second::xs = ts in
          Utils.find_pair xs (RParen, LParen)
            (fun (pre, post) -> stmt_lines post (fun (lines, rest) ->
                sc ((first::second::pre) :: lines, rest)) fc) fc
      | LCurly::xs -> Utils.find_pair xs (RCurly, LCurly)
            (fun (pre, post) -> 
                get_stmts pre (fun curlylines -> 
                    sc ([LCurly]::curlylines, post)) fc true) fc
      | _ -> find_symbol ts Semicolon [] (fun (pre, post) ->
            sc ([pre], post)) fc
 
    and get_stmts (ts : token list) 
                  (sc : token list list -> 'a) 
                  (fc : unit -> 'a) (mark : bool) : 'a = match ts with
                    [RCurly] -> if mark then sc [[RCurly]] else sc []
                  | x::xs -> stmt_lines ts (fun (prelines, post) ->
                        get_stmts post (fun lines -> sc (prelines @ lines)) fc mark) fc
                  | _ -> fc ()     


    let rec parse_args (ts : token list) 
                       (acc : (ty * string) list) : (ty * string) list = match ts with
      | (Type t)::(Identifier id)::Comma::rest -> 
              parse_args rest ((t, id)::acc)
      | (Type t)::(Identifier id)::RParen::rest ->
              List.rev ((t, id)::acc)
      | _ -> List.rev acc

    (* from a list of tokens, find the first stmt and construct it *)
    let rec stmt_construct (ts : token list)
                           (sc : statement * token list -> 'b)
                           (fc : unit -> 'b) : 'b = match ts with
        If::LParen::xs -> Utils.find_pair xs (RParen, LParen) 
            (fun (cond, post) -> 
                stmt_construct post (fun (if_stmt, rest) ->
                    match rest with
                        Else::xs' -> stmt_construct xs' (fun (else_stmt, rest') ->
                            sc (IfStmt (If::LParen::cond, if_stmt, Some else_stmt), rest')) fc
                      | _ -> sc (IfStmt (If::LParen::cond, if_stmt, None), rest)) fc) fc
      | (For::LParen::xs | While::LParen::xs) -> 
            let first::second::xs = ts in
          Utils.find_pair xs (RParen, LParen)
            (fun (cond, post) -> stmt_construct post (fun (stmt, rest) ->
                sc ((if first = For then ForStmt(first::second::cond, stmt)
                                   else WhileStmt(first::second::cond, stmt))
                        , rest)) fc) fc
      | LCurly::xs -> Utils.find_pair xs (RCurly, LCurly)
            (fun (block, post) -> 
                get_stmts block (fun blocklines ->
                    sc ((BlockStmt blocklines), post)) fc) fc
      | _ -> find_symbol ts Semicolon [] (fun (line, post) ->
            sc (SimpleStmt line, post)) fc
 
    (* get_stmts is meant to be used to construct the statement list
     * corresponding to the input of all the tokens in a block, given that the token 
     * list does not start with an LCurly. It should also be called on something 
     * terminated with an RCurly. *) 
    and get_stmts (ts : token list) 
                  (sc : statement list -> 'a) 
                  (fc : unit -> 'a) : 'a = match ts with
                    [RCurly] -> sc []
                  | x::xs -> stmt_construct ts (fun (stmt1, post) ->
                        get_stmts post (fun stmts -> sc (stmt1 :: stmts)) fc) fc
                  | _ -> fc ()

    exception InvalidParse2 of token list list

    (* Maps function name to the list of tokens of the function's code. *)
    let rec gen_function_pool (ts : token list) : func StrMap.t = 
        match demarcate_functions ts (fun res -> Some res) (fun () -> None) with 
            Some x -> 
              let nameTypeCode = List.map 
                (function (Type t)::(Identifier name)::rest as l -> (name, t, l)
                   | _ -> raise (InvalidParse2 x)) x in
              let recordMapped = List.map
                (fun (name, t, l) -> 
                    let rest = Utils.drop l 3 in
                    find_symbol rest LCurly [] (fun (args, post) ->
                        get_stmts post (fun lines -> 
                            {name = name; ty = t; args = parse_args args []; ast = BlockStmt lines})
                        (fun () -> failwith "Unable to parse statements."))
                    (fun () -> failwith "Unable to find lcurly.")) nameTypeCode in
              List.fold_left (fun dict func -> 
                let {name = name; ty = _; args = _; ast = _} = func in
                StrMap.add name func dict) (StrMap.empty) recordMapped
          | None -> failwith "Unable to generate function pool."

    let split_lines (filename : string) : func StrMap.t = 
        let (lexed, tdict, tlist) = Lexer.lex filename in 
        let fpool = gen_function_pool lexed in
        fpool
  end


