#use "Lexer.ml";;

module type PARSER =
  sig
    val split_lines : token list -> token list list
    val gen_function_pool : token list -> token list StrMap.t
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
                                (fc : unit -> 'a) = match ts with
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
      | (Type _)::name::Semicolon::xs -> demarcate_functions xs sc fc (* var decl. *)
      | (Type _)::xs -> find_symbol ts RParen []
                (fun (pre, post) -> match post with
                    Semicolon::rest -> demarcate_functions rest sc fc
                  | LCurly::rest -> Utils.find_pair rest (RCurly, LCurly)
                    (fun (pre', post') ->
                        demarcate_functions post' (fun res -> sc ((pre @ LCurly::pre')::res)) fc)
                    (fun () -> failwith "No right curly found.")
                  | _ -> failwith "No semicolon or lcurly after rparen.") fc
      | x::xs -> raise (InvalidParse (x::xs))

    let get_function_name ts = match ts with
      | (Type _)::(Identifier name)::rest -> name
      | _ -> failwith "Unable to find function name."

    (* Maps function name to the list of tokens of the function's code. *)
    let rec gen_function_pool ts = 
        match demarcate_functions ts (fun res -> Some res) (fun () -> None) with 
            Some x -> List.fold_left (fun dict func -> 
                StrMap.add (get_function_name func) func dict) (StrMap.empty) x
          | None -> failwith "Unable to generate function pool."

    let split_lines (filename : string) = 
        let (lexed, tdict, tlist) = Lexer.lex filename in 
            rd_gdecl lexed (fun x -> Some x) (fun () -> None)
  end


