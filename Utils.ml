module StrMap = Map.Make(String);;

let convoluted_name f x = f x

let (@$) = convoluted_name

type 'a res = ('a, string) result

module type UTILS =
  sig
    val explode : string -> char list
    val implode : char list -> string
    val charToStr : char -> string
    val drop : 'a list -> int -> 'a list
    val dropR : 'a list -> int -> 'a list
    val is_prefix : 'a list -> 'a list -> 'a list res
    val find_end : 'a list -> ('a * 'a) -> ('a list * 'a list) res
    val get_pair : 'a list -> ('a * 'a) -> ('a list * 'a list) res
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

    let rec is_prefix (l1 : 'a list) (l2 : 'a list) : 'a list res = 
      match (l1, l2) with
      | ([], []) -> Ok []
      | (x::xs, []) -> Error "could not find prefix"
      | ([], x::xs) -> Ok (x::xs)
      | (x::xs, y::ys) -> if x = y then is_prefix xs ys
                                   else Error "could not find prefix"

    let rec take l n = match Int.compare n 0 with
        -1 -> failwith "Negative input"
      | 0 -> []
      | 1 -> (match l with
                [] -> failwith "No more elements"
              | x::xs -> x :: (take xs (n-1)))
      | _ -> failwith "take impossible"

    let rec find_end (l : 'a list) (left, right) : ('a list * 'a list) res = 
        let rec find_end' l n acc = match (l, n) with
                (_, 0) -> Ok (List.rev acc, l)
              | ([], n) -> Error "could not find pair"
              | (x::xs, n) -> (match (x = right, x = left) with
                    (true, _) -> find_end' xs (n - 1) (x::acc)
                  | (_, true) -> find_end' xs (n + 1) (x::acc)
                  | _ -> find_end' xs n (x::acc))
        in
            find_end' l 1 []

    let rec get_pair (l : 'a list) (left, right) : ('a list * 'a list) res = 
        let rec get_pair' (l : 'a list) (n : int) (mark : bool) (acc : 'a list) =
            if mark then
                (match (l, n) with
                | (_, 0) -> Ok (List.rev acc, l)
                | ([], _) -> Error "Did not find end of pair."
                | (x::xs, _) -> 
                    (match (x = left, x = right) with
                    | (true, _) -> get_pair' xs (n + 1) true (x::acc)
                    | (_, true) -> get_pair' xs (n - 1) true (x::acc)
                    | _ -> get_pair' xs n true (x::acc)))
                    else
                (match (l, n) with
                | ([], _) -> Error "Did not see left pair before running out."
                | (x::xs, _) -> 
                    (match (x = left, x = right) with
                    | (true, _) -> get_pair' xs (n + 1) true (x::acc)
                    | (_, true) -> Error "saw right pair first."
                    | _ -> get_pair' xs n mark (x::acc))) in 
        get_pair' l 0 false []

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


let return (x : 'a) : 'a res = Ok x
let bind (x : 'a res) (op : 'a -> 'b res) : 'b res = 
    match x with
    | Error x -> Error x
    | Ok z -> op z

let (>>=) = bind
let (let*) x f = bind x f
