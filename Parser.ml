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

    exception InvalidParse of token list

    let rec demarcate_functions (ts : token list) : token list list res = 
        match ts with
          [] -> Ok []
        | Struct::name::Semicolon::xs -> demarcate_functions xs
        | Struct::rest -> 
            let* (_, post') = Utils.get_pair ts (LCurly, RCurly) in
            (match post' with
            | Semicolon::rest -> demarcate_functions rest
            | _ -> Error "No semicolon after struct decl.")
        | (Typedef::xs) -> 
            let* (_, post) = find_symbol ts Semicolon in
            demarcate_functions post
        | Use::xs -> 
            let* (_, post) = find_symbol ts RChevron in
            demarcate_functions post
        | (Type _)::xs -> 
            let* (pre, post) = Utils.get_pair ts (LParen, RParen) in
            (match post with
            | Semicolon::rest -> demarcate_functions rest (* technically not possible *)
            | LCurly::_ -> 
                let* (pre', post') = Utils.get_pair post (LCurly, RCurly) in
                let* res = demarcate_functions post' in
                Ok ((pre @ pre')::res)
            | _ -> Error "No semicolon or lcurly after rparen.")
        | x::xs -> Error "Not a valid start to the function."

    let rec parse_args (ts : token list) 
                       (acc : (ty * string) list) : (ty * string) list res = 
        match ts with
        | (Type t)::(Identifier id)::Comma::rest -> 
            parse_args rest ((t, id)::acc)
        | (Type t)::(Identifier id)::RParen::rest ->
            return @@ List.rev ((t, id)::acc)
        | _ -> return @@ List.rev acc

    (* from a list of tokens, find the first stmt and construct it *)
    let rec stmt_construct (ts : token list) : (statement * token list) res = 
        match ts with
        | If::LParen::xs ->
            let* (cond, post) = Utils.get_pair ts (LParen, RParen) in
            let* (if_stmt, rest) = stmt_construct post in
            (match rest with
            | Else::xs' -> 
                let* (else_stmt, rest') = stmt_construct xs' in
                Ok (IfStmt (cond, if_stmt, Some else_stmt), rest')
            | _ -> Ok (IfStmt (cond, if_stmt, None), rest))
        | (For::LParen::xs | While::LParen::xs) ->
            let first::_ = ts in
            let* (cond, post) = Utils.get_pair ts (LParen, RParen) in
            let* (stmt, rest) = stmt_construct post in
            return ((if first = For then ForStmt (cond, stmt)
                                   else WhileStmt (cond, stmt)), rest)
        | LCurly::xs -> 
            let* (block, post) = Utils.find_end xs (LCurly, RCurly) in
            let* blocklines = get_stmts block in
            Ok ((BlockStmt blocklines), post)
        | _ -> 
            let* (line, post) = find_symbol ts Semicolon in
            Ok (SimpleStmt line, post)
 
    (* get_stmts is meant to be used to construct the statement list
     * corresponding to the input of all the tokens in a block, given that the token 
     * list does not start with an LCurly. It should also be called on something 
     * terminated with an RCurly. *) 
    and get_stmts (ts : token list) : statement list res =
        match ts with
        | [RCurly] -> Ok []
        | x::xs -> 
            let* (stmt1, post) = stmt_construct ts in
            let* stmts = get_stmts post in
            Ok (stmt1 :: stmts)
        | _ -> Error "Statements did not end in RCurly."

    exception InvalidParse2 of token list list

    (* Maps function name to the list of tokens of the function's code. *)
    let rec gen_function_pool (ts : token list) : func StrMap.t res = 
        let* x = demarcate_functions ts in
        let nameTypeCode = List.map 
            (function (Type t)::(Identifier name)::rest as l -> (name, t, l)
            | _ -> raise (InvalidParse2 x)) x in
        let recordMapped = List.map
            (fun (name, t, l) -> 
                let rest = Utils.drop l 3 in
                let* (args, post) = find_symbol rest LCurly in
                let* lines = get_stmts post in
                let* argres = parse_args args [] in
                Ok {name = name; ty = t; args = argres; ast = BlockStmt lines})
            nameTypeCode in
        let foldedRecords = List.fold_left (fun res_dict func -> 
            match (func, res_dict) with
            | (Ok ({name = name} as reco), Ok dict) ->
                return @@ StrMap.add name reco dict 
            | _ -> Error "Error in folding.") (Ok StrMap.empty) recordMapped in
            foldedRecords

    let split_lines (filename : string) : func StrMap.t res = 
        let* (lexed, tdict, tlist) = Lexer.lex filename in 
        let* fpool = gen_function_pool lexed in
        return @@ fpool
  end


