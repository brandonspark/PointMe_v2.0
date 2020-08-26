#load "str.cma";;
#use "Utils.ml";;

type ty = Base of string
        | Ptr of ty
        | Array of ty (* name of type, and number of iterated pointers *)

let rec str_ty (t : ty) =
    match t with
    | Base b -> b
    | Ptr t -> Format.sprintf "%s*" (str_ty t)
    | Array t -> Format.sprintf "%s[]" (str_ty t)

(* yes, I'm aware it's an atrocious type. *)
type token =
   | Identifier of string 
   | StrLit of string
   | ChrLit of char
   | LibLit of string
   | Const of Int32.t
   | Bool of bool
   | Type of ty
   | Struct
   | Typedef
   | If | While | Else | For | Continue | Break | Return | Assert | Error_t
   | NULL
   | Alloc | Alloc_array
   | Use
   | LParen
   | RParen
   | LCurly
   | RCurly
   | LBracket
   | RBracket
   | Plus
   | Minus
   | Asterisk
   | Arrow
   | Equal of token option
   | Decrement
   | Increment
   | Slash
   | Bang
   | Tilde
   | Percent
   | RChevron
   | RShift
   | LChevron
   | LShift
   | Amper
   | Caret
   | Pipe
   | And
   | Or
   | QMark
   | Colon
   | Comma
   | Semicolon
   | Period
   | EqEq
   | NotEq
   | Leq
   | Geq

let rec str_token (t : token) =
    let sp = Format.sprintf in
    match t with
    | Identifier n -> n
    | StrLit s -> s
    | ChrLit c -> sp "'%c'" c
    | LibLit s -> sp "<%s>" s
    | Const n -> sp "%d" (Int32.to_int n)
    | Bool b -> if b then "true" else "false"
    | Type ty -> str_ty ty
    | Struct -> "struct"
    | Typedef -> "typedef"
    | If -> "if"
    | While -> "while"
    | Else -> "else" 
    | For -> "for"
    | Continue -> "continue"
    | Break -> "break"
    | Return -> "return"
    | Assert -> "assert"
    | Error_t -> "error"
    | NULL -> "NULL"
    | Alloc -> "alloc"
    | Alloc_array -> "alloc_array"
    | Use -> "use"
    | LParen -> "(" | RParen -> ")"
    | LCurly -> "{" | RCurly -> "}"
    | LBracket -> "[" | RBracket -> "]"
    | Plus -> "+" | Minus -> "-"
    | Asterisk -> "*" | Arrow -> "->"
    | Equal (Some t) -> (str_token t) ^ "="
    | Equal None -> "="
    | Decrement -> "--" | Increment -> "++"
    | Slash -> "/" | Bang -> "!" | Tilde -> "~" | Percent -> "%"
    | RChevron -> ">" | LChevron -> "<"
    | RShift -> ">>" | LShift -> "<<"
    | Amper -> "&" | Caret -> "^" | Pipe -> "|"
    | And -> "&&" | Or -> "||" | QMark -> "?" | Colon -> ":"
    | Comma -> "," | Semicolon -> ";" | Period -> "." | EqEq -> "=="
    | NotEq -> "!=" | Leq -> "<=" | Geq -> ">="

module type LEXER =
  sig
    type typeDict
    val programToString : string -> string
    val split : string -> string list        
    val lex : string -> (token list * typeDict * string list * (ty * string) list StrMap.t) res  
  end

module Lexer = (*: LEXER =*)
  struct
    open ResultMonad;;

    type typeDict = ty StrMap.t

    let rec programToString (fileName : string) : string =
        let input = open_in fileName in
        let s = really_input_string input (in_channel_length input) in
        close_in input; s

    (* basic tokens that are not prefixes to other operators *)
    let tokens = ['('; ')'; '{'; '}'; '['; ']'; ',';     (* separators *)
                  '~'; '.'; ';'; '?'; ':']

    (* more advanced tokens that are prefixes to other operators *)
    let tokens2 = ['*'; '/'; '!'; '%'; '='; '^'] (* standalone + = after *)
   
    (* checkFirst looks for a particular character in a list, then appends it to
     * an acccumulator in a space-separated format if the character after it
     * matches, returning the rest of the list *)
    let rec checkFirst (first : char) (rest : char list) (ref : char list) (acc : char list) =
        match rest with
            [] -> (rest, ' '::first::' '::acc)
          | second::xs -> if List.mem second ref then (xs, ' '::second::first::' '::acc)
                                       else (rest, ' '::first::' '::acc)
    
    (* some lists for the suffixes to operators that start with -, +, &, and |,
     * respectively *)
    let minusList = ['>'; '-'; '=']
    let plusList = ['+'; '=']
    let ampList = ['&'; '=']
    let pipeList = ['|'; '=']

    let rec remove_comments1 (cs : char list) (acc : char list) (cmark : bool) : char list =
        if cmark then
        (match cs with
            [] -> acc
          | '\n'::xs -> remove_comments1 xs acc false
          | x::xs -> remove_comments1 xs acc cmark)
                 else
        (match cs with
            [] -> acc
          | '/'::'/'::xs -> remove_comments1 xs acc true
          | x::xs -> remove_comments1 xs (x::acc) cmark)

    let rec remove_comments2 (cs : char list) (acc : char list) (cmark : bool) : char list =
        if cmark then
            (match cs with
                [] -> acc
              | '*'::'/'::xs -> remove_comments2 xs acc false
              | x::xs -> remove_comments2 xs acc cmark)
                 else
            (match cs with
                [] -> acc
              | '/'::'*'::xs -> remove_comments2 xs acc true
              | x::xs -> remove_comments2 xs (x::acc) cmark)

    (* spaceOut takes in a char list of text in a file and transforms it into a
     * space-separated character list, based on operators. *)
    let rec spaceOut (cs : char list) (acc : char list) (quoteMark : bool) : char list =
        if quoteMark then
        (match cs with
            [] -> acc
          | '\\'::'"'::xs -> spaceOut xs ('"'::'\\'::acc) quoteMark
          | '\''::'"'::'\''::xs -> spaceOut xs ('\''::'"'::'\''::acc) quoteMark
          | '"'::xs -> spaceOut xs ('"'::acc) (not quoteMark)
          | x::xs -> spaceOut xs (x::acc) quoteMark)
        else
        (match cs with
            [] -> acc
          | '\\'::'"'::xs -> spaceOut xs ('"'::'\\'::acc) quoteMark
          | '\''::'"'::'\''::xs -> spaceOut xs ('\''::'"'::'\''::acc) quoteMark
          | '"'::xs -> spaceOut xs ('"'::acc) (not quoteMark)
          | '\t'::xs -> spaceOut xs (' '::acc) quoteMark
          | '\n'::xs -> spaceOut xs (' '::acc) quoteMark
          | '-'::xs -> let (rest, acc') = checkFirst '-' xs minusList acc in
                       spaceOut rest acc' quoteMark
          | '+'::xs -> let (rest, acc') = checkFirst '+' xs plusList acc in
                       spaceOut rest acc' quoteMark
          | '&'::xs -> let (rest, acc') = checkFirst '&' xs ampList acc in
                       spaceOut rest acc' quoteMark
          | '|'::xs -> let (rest, acc') = checkFirst '|' xs pipeList acc in
                       spaceOut rest acc' quoteMark
          | '>'::xs -> (match xs with 
                       | '='::xs' -> spaceOut xs' (' '::'='::'>'::' '::acc) quoteMark
                       | '>'::'='::xs' -> spaceOut xs' (' '::'='::'>'::'>'::' '::acc) quoteMark
                       | '>'::xs' -> spaceOut xs' (' '::'>'::'>'::' '::acc) quoteMark
                       | _ -> spaceOut xs (' '::'>'::' '::acc) quoteMark)
          | '<'::xs -> (match xs with
                       | '='::xs' -> spaceOut xs' (' '::'='::'<'::' '::acc) quoteMark
                       | '<'::'='::xs' -> spaceOut xs' (' '::'='::'<'::'<'::' '::acc) quoteMark
                       | '<'::xs' -> spaceOut xs' (' '::'<'::'<'::' '::acc) quoteMark
                       | _ -> spaceOut xs (' '::'<'::' '::acc) quoteMark)
          | x::xs -> if List.mem x tokens then spaceOut xs (' '::x::' '::acc) quoteMark
                else if List.mem x tokens2 then 
                     let (rest, acc') = checkFirst x xs ['='] acc in
                        spaceOut rest acc' quoteMark
                      else spaceOut xs (x::acc) quoteMark)
    
    (* removeDupes gets rid of duplicate spaces *)
    let rec removeDupes (cs : char list) (acc : char list) : char list =
        match cs with
            [] -> acc
          | ' '::[] -> acc
          | ' '::' '::xs -> removeDupes (' '::xs) acc
          | x::xs -> removeDupes xs (x::acc)
    
    (* splitSpaces takes in a char list and splits it into different strings,
     * which it stores in an accumulator, based on the spaces present in the
     * list. *)
    let rec splitSpaces (cs : char list) = match cs with
        [] -> (false, "", [])
      | '\\'::'"'::xs ->
              let (flag, s, ss) = splitSpaces xs in (flag, "\"" ^ s, ss)
      | '\''::'"'::'\''::xs ->
              let (flag, s, ss) = splitSpaces xs in (flag, "", if s = "" then 
                  "'\"'"::ss else "'\"'"::s::ss)
      | x::xs ->
        let (flag, s, ss) = splitSpaces xs in
        if flag then
            (match x with  
                '"' -> (false, Utils.charToStr '"' ^ s, ss)
              | _ -> (true, Utils.charToStr x ^ s, ss))
        else
            (match x with
                '"' -> (true, Utils.charToStr '"' ^ s, ss)
              | ' ' -> (false, "", if s = "" then ss else s::ss)
              | _ -> (false, Utils.charToStr x ^ s, ss))

    (* split, given the name of a c0 file, splits it into a string list of all
     * of the constituent tokens in the program *)
    let split (fileName : string) : string list =
        let programString = programToString fileName in
        let noComments1 = remove_comments1 (Utils.explode programString) [] false in
        let noComments2 = remove_comments2 noComments1 [] false in
        let spaced = spaceOut (noComments2) [] false in
        let noDupes = removeDupes spaced [] in
        let buf = Buffer.create (List.length noDupes) in
        let () = List.iter (Buffer.add_char buf) noDupes in
        let (_, s, ss) = splitSpaces (noDupes) in
            match s with
                "" -> ss
              | _ -> s::ss

    module Local1 =
      struct
        open ListStateResMonad

        let rec get_type (acc : ty) = fun ss ->
            let rec get_type' (l : string list) (acc : ty) : (ty * string list) res = 
                match l with 
                | "*"::xs -> get_type' xs (Ptr acc)
                | "["::"]"::xs -> get_type' xs (Array acc)
                | _ -> Ok (acc, l) in
            get_type' ss acc
            
        let rec get_type_t (acc : ty) = fun ts ->
            let rec get_type_t' (l : token list) (acc : ty) = 
                match l with
                | Asterisk::xs -> get_type_t' xs (Ptr acc) 
                | LBracket::RBracket::xs -> get_type_t' xs (Array acc)
                | _ -> Ok (acc, l) in
            get_type_t' ts acc

        (* typedict_init, given a string list of the separated tokens, adds all the
         * relationships created by typedefs in the program. It maps the new names
         * to the old names. Notably, if the old name was a struct, the canonical
         * name of that type has a "s_" prepended to it. *)
        let rec typedict_init (d : typeDict) : (typeDict, 'a) m = fun l ->
          match l with 
          | [] -> Ok (d, [])
          | "typedef"::"struct"::oldname::rest
          | "typedef"::oldname::rest -> 
                let prefix = (match l with "typedef"::"struct"::_::_ -> "s_" | _ -> "") in
                runState rest @@
                let+ ty      = get_type (Base (prefix ^ oldname)) in
                let+ newname = pop in
                let+ _       = find_symbol ";" in
                let+ tdict = typedict_init (StrMap.add newname ty d) in
                return_both tdict
                (*eval return_both @@ typedict_init (StrMap.add newname ty d) *)
          | x::xs -> 
                runState xs @@
                let+ res = typedict_init d in
                return_both res 
                (*runState xs @@ eval return_both @@ typedict_init d
*)
        (* gen_typelist, give a string list of the separated tokens in the program,
         * adds on all of the new types initialized by struct declarations in "s_"
         * prepended form to an accumulator list. these effectively form the set of
         * "canonical types" for the program, that are their own most simplified
         * forms. *)
        let rec gen_typelist (acc : string list) : (string list, string) m =
            function
            | [] -> Ok (acc, [])
            | "struct"::sid::"{"::rest ->
                runState rest @@
                let+ _     = find_symbol "}" in
                let+ ()    = expect ";" in
                let+ tlist = gen_typelist (("s_" ^ sid)::acc) in
                return_both tlist
            | "struct"::sid::";"::rest -> 
                runState rest @@
                let+ tlist = gen_typelist (("s_" ^ sid)::acc) in
                return_both tlist
            | x::xs -> 
                runState xs @@
                let+ tlist = gen_typelist acc in
                return_both tlist
    end 
    include Local1 

    (* a function for navigating the type dict, to find the canonical type. *)
    let rec reduce_type (t : ty) (typeList : string list) (tdict : typeDict) : ty res = 
        let rec reduce_type' (t : ty) = 
            match t with
            | Base s -> 
                if StrMap.mem s tdict then reduce_type' (StrMap.find s tdict)
                                      else (if List.mem s typeList then Ok t
                                                    else Error "Cannot resolve type")
            | Ptr p -> 
                let* new_ty = reduce_type' p in
                Ok (Ptr new_ty)
            | Array a ->
                let* new_ty = reduce_type' a in
                Ok (Array new_ty) in
        reduce_type' t 

    (* hasLast checks if a char list has a last character of the provided
     * character *)
    let hasLast (rest : char list) (c : char) = match rest with
        [] -> false
      | _ -> List.nth rest (List.length rest - 1) = c

    (* is_printable uses ASCII hacks to tell you if a char is "printable" *)
    let is_printable (c: char) =
        if Char.code c >= 32 && Char.code c <= 126 then true
                                         else false

    (* matchRest, given a char list of all the characters in a given token,
     * tries to match it to the token that it represents. 
     * matchRest covers things like string literals, char literals, lib
     * literals, numbers, keywords, types, and identifiers. *)
    let matchRest (cs : char list) (tdict : typeDict) (tlist : string list) : token = match cs with
        [] -> failwith "No match possible.\n"
      | '"'::rest -> if hasLast rest '"' then 
                        StrLit (Utils.implode (Utils.dropR rest 1))
                    else failwith "Invalid string literal"
      | '\''::rest -> if hasLast rest '\'' then
                        if List.length rest = 2 && is_printable (List.nth rest 0) then
                            ChrLit (List.nth rest 0)
                        else (match rest with
                            ['\\'; 'n'] -> ChrLit '\n'
                          | ['\\'; 't'] -> ChrLit '\t'
                          | ['\\'; 'b'] -> ChrLit '\b'
                          | ['\\'; 'r'] -> ChrLit '\r'
                          | ['\\'; '\''] -> ChrLit '\''
                          | _ -> failwith "Invalid char")
                      else failwith "No ending apostrophe found.\n"
      | '<'::rest -> if hasLast rest '>' then LibLit (Utils.implode (Utils.dropR rest 1))
                                         else failwith "No ending chevron found"
      | _ -> try Const (Int32.of_int @@ int_of_string (Utils.implode cs)) with int_of_string ->
                let s = Utils.implode cs in
                (match Utils.implode cs with
                    "int" ->  Type (Base "int")
                  | "bool" -> Type (Base "bool")
                  | "string" -> Type (Base "string")
                  | "char" -> Type (Base "char")
                  | "void" -> Type (Base "void")
                  | "struct" -> Struct 
                  | "typedef" -> Typedef 
                  | "if" -> If
                  | "else" -> Else
                  | "while" -> While
                  | "for" -> For
                  | "continue" -> Continue
                  | "break" -> Break
                  | "return" -> Return
                  | "assert" -> Assert
                  | "true" -> Bool true
                  | "false" -> Bool false
                  | "NULL" -> NULL
                  | "alloc" -> Alloc
                  | "alloc_array" -> Alloc_array 
                  | "error" -> Error_t
                  | _ -> if (List.mem s tlist) || (StrMap.mem s tdict) then
                            Type (Base s)
                         else 
                             if List.mem ("s_" ^ s) tlist then Type (Base ("s_" ^ s))
                                                             else Identifier s)
      
  (* matcher looks at a string that represents a token and tries to determine
   * that token it is. if it isn't one of the obvious ones, then it is passed to
   * matchRest, which does more advanced parsing. *)
  let matcher (s : string) (tdict : typeDict) (tlist : string list) : token = match s with
        "(" -> LParen
      | ")" -> RParen 
      | ";" -> Semicolon
      | "." -> Period
      | "," -> Comma
      | "[" -> LBracket
      | "]" -> RBracket
      | "{" -> LCurly
      | "}" -> RCurly
      | "-" -> Minus
      | "--" -> Decrement 
      | "->" -> Arrow
      | "-=" -> Equal (Some Minus)
      | "*" -> Asterisk
      | "*=" -> Equal (Some Asterisk)
      | "+" -> Plus
      | "++" -> Increment
      | "+=" -> Equal (Some Plus)
      | "/" -> Slash
      | "/=" -> Equal (Some Slash)
      | "!" -> Bang
      | "!=" -> NotEq
      | "~" -> Tilde
      | "%" -> Percent
      | "%=" -> Equal (Some Percent)
      | ">" -> RChevron
      | ">=" -> Geq
      | ">>" -> RShift
      | ">>=" -> Equal (Some RShift)
      | "=" -> Equal None
      | "==" -> EqEq
      | "&" -> Amper
      | "&=" -> Equal (Some Amper)
      | "&&" -> And
      | "^" -> Caret
      | "^=" -> Equal (Some Caret)
      | "|" -> Pipe
      | "|=" -> Equal (Some Pipe)
      | "||" -> Or
      | "?" -> QMark
      | ":" -> Colon
      | "<" -> LChevron
      | "<=" -> Leq
      | "<<" -> LShift 
      | "<<=" -> Equal (Some LShift)
      | "#use" -> Use 
      | _ -> matchRest (Utils.explode s) tdict tlist

    module Local2 =
      struct
        open ListStateResMonad

        let rec consolidate_types (acc : token list) : ('a list, token) m =
            function
            | (Type t)::rest -> 
                runState rest @@
                let+ ty = get_type_t t in
                let+ final = consolidate_types ((Type ty)::acc) in
                return_both final
            | [] -> Ok (acc, [])
            | x::xs -> 
                runState xs @@
                let+ final = consolidate_types (x::acc) in
                return_both final

        let rec parse_fields (l : token list) (acc : (ty * string) list) : (ty * string) list = 
            match l with
            | Struct::(Type t)::(Identifier id)::Semicolon::rest
            | (Type t)::(Identifier id)::Semicolon::rest -> 
                parse_fields rest ((t, id)::acc)
            | _ -> (List.rev acc)

        let rec get_structinfo (acc : (ty * string) list StrMap.t) : ((ty * string) list StrMap.t, token) m = fun l ->
            match l with 
            | Struct::(Type (Base name))::LCurly::xs ->
                runState xs @@
                let+ arglist = find_end (LCurly, RCurly) in
                let  fields  = parse_fields arglist [] in
                eval return_both @@ get_structinfo (StrMap.add name fields acc)
            | x::xs -> 
                runState xs @@
                eval return_both @@ get_structinfo acc
            | [] -> Ok (acc, [])
      end
    include Local2

    let rec remove_token (t : token) (ts : token list) (acc : token list) : token list =
        match ts with
        | [] -> List.rev acc
        | x::xs -> if t = x then remove_token t xs acc
                            else remove_token t xs (x::acc)

    (* lex finally lexes the entirety of the file. *)
    let lex (fileName : string) : (token list * typeDict * string list * (ty * string) list StrMap.t) res =
        let slist = split fileName in
        let* tdict = ListStateResMonad.runState slist @@ typedict_init (StrMap.empty) in
        let* tlist = ListStateResMonad.runState slist @@ gen_typelist ["int"; "bool"; "void"; "string"; "char"] in
        let tokens = List.map (fun s -> matcher s tdict tlist) slist in 
        let* types_parsed = ListStateResMonad.runState tokens @@ consolidate_types [] in
        let* sinfo = ListStateResMonad.runState (List.rev types_parsed) @@ get_structinfo (StrMap.empty) in
        (*let new_tokens = remove_token Struct types_parsed [] in*)
        return @@ (List.rev types_parsed, tdict, tlist, sinfo)

end;;

