#load "str.cma";;

type ty = string * int (* name of type, and number of iterated pointers *)

module TypeMap = Map.Make(String);;

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
   | If | While | Else | For | Continue | Break | Return | Assert
   | NULL
   | Alloc | Alloc_array
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
   | Leq
   | Geq


module Lexer =
struct

    type typeDict = (string * int) TypeMap.t

    let rec programToString (fileName : string) : string =
        let input = open_in fileName in
        let s = really_input_string input (in_channel_length input) in
        close_in input; s

    (* turns a string into its char list representation *)
    let explode (s : string) : char list = List.init (String.length s) (String.get s)

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
    
    (* basic charToStr function for particular escaped characters. *)
    let rec charToStr (c : char) = 
        match c with
            '\n' -> "\n"
          | '\r' -> "\r"
          | '\t' -> "\t"
          | '\b' -> "\b"
          | '\'' -> "'"
          | '\\' -> "\\"
          | '"' -> "\""
          | _ -> Char.escaped c

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
                '"' -> (false, charToStr '"' ^ s, ss)
              | _ -> (true, charToStr x ^ s, ss))
        else
            (match x with
                '"' -> (true, charToStr '"' ^ s, ss)
              | ' ' -> (false, "", if s = "" then ss else s::ss)
              | _ -> (false, charToStr x ^ s, ss))

    (* implode turns a char list back into a string *)
    let implode (cs : char list) : string =
        let buf = Buffer.create(List.length cs) in
        let () = List.iter (Buffer.add_char buf) cs in
        Buffer.contents buf

    (* split, given the name of a c0 file, splits it into a string list of all
     * of the constituent tokens in the program *)
    let split (fileName : string) : string list =
        let programString = programToString fileName in
        let noComments1 = remove_comments1 (explode programString) [] false in
        let noComments2 = remove_comments2 noComments1 [] false in
        let spaced = spaceOut (noComments2) [] false in
        let noDupes = removeDupes spaced [] in
        let buf = Buffer.create (List.length noDupes) in
        let () = List.iter (Buffer.add_char buf) noDupes in
        let (_, s, ss) = splitSpaces (noDupes) in
            match s with
                "" -> ss
              | _ -> s::ss

    (* countSymbol is a CPS function that counts the number of times that a
     * symbol appears in the prefix of a list, and calls sc on that number and
     * the remainder of the list. *)
    let rec countSymbol (ss : string list) (target : string)
                        (sc : int * string list -> 'a) = match ss with
        [] -> sc (0, [])
      | x::xs -> if x = target then 
          countSymbol xs target (fun (n, l) -> sc (n + 1, l))
                               else sc (0, x::xs)

    (* find_symbol is a CPS function that finds the first occurrence of some
     * character in a list, then returns the rest of the list after it. *)
    let rec find_symbol (ss : string list) (target : string) 
                          (sc : string list -> 'a) (fc : unit -> 'a) = match ss with
        [] -> fc ()
      | x::xs -> if x = target then sc xs
                               else find_symbol xs target sc fc       
    
    (* typedict_init, given a string list of the separated tokens, adds all the
     * relationships created by typedefs in the program. It maps the new names
     * to the old names. Notably, if the old name was a struct, the canonical
     * name of that type has a "s_" prepended to it. *)
    let rec typedict_init (ss : string list) (d : typeDict) : typeDict = match ss with
        [] -> d
      | "typedef"::"struct"::oldname::rest ->
            countSymbol rest "*"
                (fun (num, rest1) -> match rest1 with
                    [] -> failwith "No name for typedef."
                  | newname::rest2 -> find_symbol rest2 ";"
                    (fun rest3 -> typedict_init rest3 (TypeMap.add newname ("s_"^ oldname, num) d))
                    (fun () -> failwith "Unable to find semicolon."))
      | "typedef"::oldname::rest -> 
            countSymbol rest "*" 
                (fun (num, rest1) -> match rest1 with
                    [] -> failwith "No name for typedef."
                  | newname::rest2 -> 
        find_symbol rest2 ";" 
                    (fun rest3 -> typedict_init rest3 (TypeMap.add newname (oldname, num) d))
                    (fun () -> failwith "Unable to find semicolon."))
      | x::xs -> typedict_init xs d

    (* get_typelist, give a string list of the separated tokens in the program,
     * adds on all of the new types initialized by struct declarations in "s_"
     * prepended form to an accumulator list. these effectively form the set of
     * "canonical types" for the program, that are their own most simplified
     * forms. *)
    let rec get_typelist (ss : string list) (acc : string list) : string list = match ss with
        [] -> acc
      | "struct"::sid::"{"::rest -> 
            find_symbol rest "}" (fun rest' -> 
                (match rest' with
                  ";"::rest'' -> get_typelist rest'' (("s_" ^ sid)::acc)
                | _ -> failwith "Did not find semicolon after right curly.\n"))
                (fun () -> failwith "Could not find right curly.\n")
      | "struct"::sid::";"::rest -> get_typelist rest (("s_" ^ sid)::acc)
      | x::xs -> get_typelist xs acc

    (* a function for navigating the type dict, to find the canonical type. *)
    let rec findCanonicalType (s : string) (typeList : string list) (tdict : typeDict) = 
        try (List.find (fun elem -> elem = s) typeList, 0) with Not_found -> 
            let (t, n) = TypeMap.find s tdict in
            let (ct, n') = findCanonicalType t typeList tdict in
            (ct, n + n')

    (* hasLast checks if a char list has a last character of the provided
     * character *)
    let hasLast (rest : char list) (c : char) = match rest with
        [] -> false
      | _ -> List.nth rest (List.length rest - 1) = c

    (* is_printable uses ASCII hacks to tell you if a char is "printable" *)
    let is_printable (c: char) =
        if Char.code c >= 32 && Char.code c <= 126 then true
                                         else false

    (* take function for lists *)
    let rec take l n = match Int.compare n 0 with
        -1 -> failwith "Negative input"
      | 0 -> l
      | 1 -> (match l with
                [] -> failwith "No more elements"
              | x::xs -> take xs (n-1))
      | _ -> failwith "take impossible"

    (* drop function for lists that drops from the back *)
    let rec drop l n = List.rev (take (List.rev l) n)

    (* matchRest, given a char list of all the characters in a given token,
     * tries to match it to the token that it represents. 
     * matchRest covers things like string literals, char literals, lib
     * literals, numbers, keywords, types, and identifiers. *)
    let matchRest (cs : char list) (tdict : typeDict) (tlist : string list) : token = match cs with
        [] -> failwith "No match possible.\n"
      | '"'::rest -> if hasLast rest '"' then 
                        StrLit (implode (drop rest 1))
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
      | '<'::rest -> if hasLast rest '>' then LibLit (implode (drop rest 1))
                                         else failwith "No ending chevron found"
      | _ -> try Const (int_of_string (implode cs)) with int_of_string ->
                let s = implode cs in
                (match implode cs with
                    "int" ->  Type ("int", 0)
                  | "bool" -> Type ("bool", 0)
                  | "string" -> Type ("string", 0)
                  | "char" -> Type ("char", 0)
                  | "void" -> Type ("void", 0)
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
                  | _ -> if (List.mem s tlist) || (TypeMap.mem s tdict) then
                            Type (s, 0)
                         else 
                             if List.mem ("s_" ^ s) tlist then Type ("s_" ^ s, 0)
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
      | "!=" -> Equal (Some Bang)
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
      | _ -> matchRest (explode s) tdict tlist

    (* lex finally lexes the entirety of the file. *)
    let lex (fileName : string) : token list * typeDict * string list =
        let slist = split fileName in
        let tdict = typedict_init slist (TypeMap.empty) in
        let tlist = get_typelist slist ["int"; "bool"; "void"; "string"; "char"] in
        (List.map (fun s -> matcher s tdict tlist) slist, tdict, tlist)
end;;
