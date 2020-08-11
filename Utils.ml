module StrMap = Map.Make(String);;

module type UTILS =
  sig
    val explode : string -> char list
    val implode : char list -> string
    val charToStr : char -> string
    val drop : 'a list -> int -> 'a list
    val dropR : 'a list -> int -> 'a list
    val is_prefix : 'a list -> 'a list -> ('a list -> 'b) -> (unit -> 'b) -> 'b
    val find_pair : 'a list -> ('a * 'a) -> ('a list * 'a list -> 'b) -> (unit -> 'b) -> 'b
    val take : 'a list -> int -> 'a list
    val dict_to_list : 'a StrMap.t -> (string * 'a) list
    val take_two : 'a list -> 'a * 'a
    val print_blue : string -> unit
  end

module Utils : UTILS =
  struct
    let explode (s : string) : char list = List.init (String.length s) (String.get s)
    let implode (cs : char list) : string =
        let buf = Buffer.create(List.length cs) in
        let () = List.iter (Buffer.add_char buf) cs in
        Buffer.contents buf
    
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
    
    (* drop function for lists *)
    let rec drop l n = match Int.compare n 0 with
        -1 -> failwith "Negative input"
      | 0 -> l
      | 1 -> (match l with
                [] -> failwith "No more elements"
              | x::xs -> drop xs (n-1))
      | _ -> failwith "drop impossible"

    (* reverse drop function for lists that drops from the back *)
    let dropR l n = List.rev (drop (List.rev l) n)

    let rec is_prefix (l1 : 'a list) (l2 : 'a list)
                      (sc : 'a list -> 'b)
                      (fc : unit -> 'b) = match (l1, l2) with
        ([], []) -> sc []
      | (x::xs, []) -> fc ()
      | ([], x::xs) -> sc (x::xs)
      | (x::xs, y::ys) -> if x = y then is_prefix xs ys sc fc
                                   else fc ()

    let rec take l n = match Int.compare n 0 with
        -1 -> failwith "Negative input"
      | 0 -> []
      | 1 -> (match l with
                [] -> failwith "No more elements"
              | x::xs -> x :: (take xs (n-1)))
      | _ -> failwith "take impossible"

    let rec find_pair (l : 'a list) (right, left)
                      (sc : 'a list * 'a list -> 'b)
                      (fc : unit -> 'b) = 
        let rec find_pair' l n acc = match (l, n) with
                (_, 0) -> sc (List.rev acc, l)
              | ([], n) -> fc ()
              | (x::xs, n) -> (match (x = right, x = left) with
                    (true, _) ->
                    find_pair' xs (n - 1) (x::acc)
                  | (_, true) ->
                    find_pair' xs (n + 1) (x::acc)
                  | _ ->
                    find_pair' xs n (x::acc))
        in
            find_pair' l 1 []

    let rec dict_to_list (d : 'a StrMap.t) =
        let seq = StrMap.to_seq d in
        Seq.fold_left (fun a b -> b::a) [] seq

    let take_two (l : 'a list) = match l with
        x::y::xs -> (x, y)
      | _ -> failwith "Unable to take two from this list."

    let print_blue (s : string) = 
        let () = print_string "\027[94m" in 
        let () = print_string s in 
        print_string "\027[0m"
  end

