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
   | Const of int
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
    | Const n -> sp "%d" n
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

(* countSymbol is a CPS function that counts the number of times that a
 * symbol appears in the prefix of a list, and calls sc on that number and
 * the remainder of the list. *)
let rec count_symbol (ss : string list) (target : string) : (int * string list) res = 
    match ss with
    | [] -> Ok (0, [])
    | x::xs -> if x = target then 
                    let* (n, l) = (count_symbol xs target) in Ok (n + 1, l)
                             else Ok (0, x::xs)

(* find_symbol is a CPS function that finds the first occurrence of some
 * character in a list, then returns the list to the left of it, inclusive on
 * the symbol, as well as the list to the right of the symbol *)
let rec find_symbol (l : 'a list) (target : 'a) : ('a list * 'a list) res =
    let rec find_symbol' (l : 'a list) (target : 'a) (acc : 'a list) =
        match l with
        | [] -> Error "Could not find symbol."
        | x::xs -> if x = target then Ok (List.rev (x::acc), xs)
                                  else find_symbol' xs target (x::acc) in
    find_symbol' l target []

(* find_symbols is a CPS function that finds the first occurrence of some
 * sequnece of symbols in a list, then returns the list to the left of it,
 * inclusive on the sequence of symbols, as well as the list to the right of the
 * sequence. *)
let rec find_symbols (l : 'a list) (targets : 'a list) : ('a list * 'a list) res = 
    match (l, targets) with
    | ([], []) -> Ok ([], [])
    | (x::xs, []) -> Ok ([], x::xs)
    | (_, y::ys) -> let* (pre, rest) = (find_symbol l y) in
                    let* post = Utils.is_prefix ys rest in
                    return (pre @ ys, post)

module type LEXER =
  sig
    type typeDict
    val programToString : string -> string
    val split : string -> string list        
    val typedict_init : string list -> typeDict -> typeDict res 
    val gen_typelist : string list -> string list -> string list res
    val lex : string -> (token list * typeDict * string list) res  
  end

module Lexer : LEXER =
  struct

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

    let rec get_type (ss : string list) (acc : ty) : (ty * string list) res = 
        match ss with
        "*"::xs -> get_type xs (Ptr acc)
      | "["::"]"::xs -> get_type xs (Array acc)
      | _ -> Ok (acc, ss)
    
    let rec get_type_t (ts : token list) (acc : ty) : (ty * token list) res = 
      match ts with
        Asterisk::xs -> get_type_t xs (Ptr acc) 
      | LBracket::RBracket::xs -> get_type_t xs (Array acc)
      | _ -> Ok (acc, ts)

    (* typedict_init, given a string list of the separated tokens, adds all the
     * relationships created by typedefs in the program. It maps the new names
     * to the old names. Notably, if the old name was a struct, the canonical
     * name of that type has a "s_" prepended to it. *)
    let rec typedict_init (ss : string list) (d : typeDict) : typeDict res = 
      match ss with
      | [] -> Ok d
      | "typedef"::"struct"::oldname::rest ->
            let* (ty, rest1) = get_type rest (Base ("s_" ^ oldname)) in
            (match rest1 with
            | [] -> Error "Nothing after the type."
            | newname::rest2 -> 
                let* (_, rest3) = find_symbol rest2 ";" in
                typedict_init rest3 (StrMap.add newname ty d))
      | "typedef"::oldname::rest -> 
            let* (ty, rest1) = get_type rest (Base oldname) in
            (match rest1 with
            | [] -> Error "No type to typedef to."
            | newname::rest2 -> 
                let* (_, rest3) = find_symbol rest2 ";" in
                typedict_init rest3 (StrMap.add newname ty d))
      | x::xs -> typedict_init xs d

    (* gen_typelist, give a string list of the separated tokens in the program,
     * adds on all of the new types initialized by struct declarations in "s_"
     * prepended form to an accumulator list. these effectively form the set of
     * "canonical types" for the program, that are their own most simplified
     * forms. *)
    let rec gen_typelist (ss : string list) (acc : string list) : string list res = match ss with
        [] -> Ok acc
      | "struct"::sid::"{"::rest -> 
            let* (_, rest') = find_symbol rest "}" in
            (match rest' with
            | ";"::rest'' -> gen_typelist rest'' (("s_" ^ sid)::acc)
            | _ -> Error "Did not find semicolon after right curly.\n")
      | "struct"::sid::";"::rest -> gen_typelist rest (("s_" ^ sid)::acc)
      | x::xs -> gen_typelist xs acc

    (* a function for navigating the type dict, to find the canonical type. *)
    (*let rec findCanonicalType (s : string) (typeList : string list) (tdict : typeDict) = 
        try (List.find (fun elem -> elem = s) typeList, 0) with Not_found -> 
            match StrMap.find s tdict with
                Ptr t ->
              | Array t ->
              | Base t -> 
            let (ct, n') = findCanonicalType t typeList tdict in
            (ct, n + n')*)

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
      | _ -> try Const (int_of_string (Utils.implode cs)) with int_of_string ->
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

    let rec consolidate_types (ts : token list) (acc : token list) = match ts with
        (Type t)::rest -> 
            let* (ty, rest') = get_type_t rest t in
            consolidate_types rest' ((Type ty)::acc)
      | [] -> Ok acc
      | x::xs -> consolidate_types xs (x::acc)
        
    (* lex finally lexes the entirety of the file. *)
    let lex (fileName : string) : (token list * typeDict * string list) res =
        let slist = split fileName in
        let* tdict = typedict_init slist (StrMap.empty) in
        let* tlist = gen_typelist slist ["int"; "bool"; "void"; "string"; "char"] in
        let tokens = List.map (fun s -> matcher s tdict tlist) slist in
        let* types_parsed = consolidate_types tokens [] in
        return @@ (List.rev types_parsed, tdict, tlist)
end;;
