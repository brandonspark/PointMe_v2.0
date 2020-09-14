module StrMap = Map.Make(String);;
module IntMap = Map.Make(Int);;

type 'a res = ('a, string) result

module type MONAD =
  sig
    type 'a m
    val return : 'a -> 'a m
    val (>>=) : 'a m -> ('a -> 'b m) -> 'b m
  end 

module type UTILS =
  sig
    val explode : string -> char list
    val implode : char list -> string
    val charToStr : char -> string
    val drop : 'a list -> int -> 'a list
    val dropR : 'a list -> int -> 'a list
    val is_prefix : 'a list -> 'a list -> 'a list res
    val take : 'a list -> int -> 'a list
    val dict_to_list : 'a StrMap.t -> (string * 'a) list
    val str_dict : ('a -> string) -> 'a StrMap.t -> string 
    val take_two : 'a list -> 'a * 'a
    val print_blue : string -> unit
    val print_red : string -> unit
    val print_purple : string -> unit
    val print_yellow : string -> unit
    val zip : 'a list -> 'b list -> ('a * 'b) list
    val print_list : ('a -> string) -> 'a list -> unit
    val list_to_str : ('a -> string) -> 'a list -> string
    val print_opt :  ('a -> string) -> 'a option -> string
  end

module ResultMonad : sig
                       include MONAD
                       val (let*) : 'a m -> ('a -> 'b m) -> 'b m
                     end with type 'a m = 'a res =
  struct
    type 'a m = 'a res
    let return (x : 'a) = Ok x
    let bind (x : 'a m) (f : 'a -> 'b m) : 'b m = 
        match x with
        | Error e -> Error e
        | Ok v -> f v 
    let (>>=) = bind
    let (let*) = bind
  end 

module ListStateResMonad =
  struct
    type 'a mstate = 'a list
    type ('v, 'a) m = 'a mstate -> ('v * 'a mstate) res

    (* returns a monadic computation that will return the input *)
    let return (x : 'v) : ('v, 'a) m = fun s -> Ok (x, s)
    
    (* gets you the state *)
    let get : ('a mstate, 'a) m = fun s -> Ok (s, s)

    (* replaces the state *)
    let put (s : 'a mstate) : (unit, 'a) m = fun s' -> Ok ((), s)

    (* bind. *)
    let bind (x : ('v, 'a) m) (f : 'v -> ('b, 'a) m) : ('b, 'a) m =
        fun initState ->
            match x initState with 
            | Error e -> Error e 
            | Ok (res, newState) ->
                let newComputation = f res in
                newComputation newState

    let (>>=) = bind
    let (let+) x f = bind x f

    (* return_both evals to a monadic computation whose value is both input and state *)
    let return_both (x : 'v) : ('v * 'a mstate, 'a) m = fun s -> Ok ((x, s), s)

    (* return_opt unpacks a res and is a comp. whose value is that res' value *)
    let return_opt (x : 'v res) : ('v, 'a) m = 
        fun s -> ResultMonad.(>>=) x (fun v -> Ok (v, s))
    
    let return_err (s : string) : ('b, 'a) m = fun _ -> Error s
    
    (* opt_bind f if the input is an Ok *)
    let opt_bind (x : 'v res) (f : 'v -> ('b, 'a) m) : ('b, 'a) m =
        fun s ->
        match x with 
        | Error e -> Error e
        | Ok v -> 
            let newComputation = f v in
            newComputation s

    (* eval will use a mode (return, return_both) and a monad and just
     * return the result of the monad using that mode *)
    let eval (mode : 'v -> ('b, 'a) m) (x : ('v, 'a) m) =
        x >>= (fun res -> mode res)

    (* runState takes in a state and monad and returns the monad's result *)
    let runState (s : 'a mstate) (p : ('v, 'a) m) : 'v res = 
        ResultMonad.(>>=) (p s) (fun (v, s) -> Ok v)

    (* suspend ignores the current state and does a monad's computation with a
     * state given as parameter, then puts the current state back *)
    let suspend (s : 'a mstate) (p : ('v, 'a) m) : ('v, 'a) m =
        fun initState ->
            match p s with
            | Error e -> Error e
            | Ok (res, newState) ->
                Ok (res, initState)

    let expect (t : 'a) : (unit, 'a) m = 
        function
        | [] -> Error "Did not find expected item."
        | x::xs -> if x = t then Ok ((), xs) 
                            else Error "did not find expected item."

    let pop : ('a, 'a) m = 
        function 
        | [] -> Error "Cannot pop from empty list."
        | x::xs -> Ok (x, xs)

    let peek : ('a, 'a) m =
        function
        | [] -> Error "Canont peek from empty list"
        | x::xs -> Ok (x, x::xs)

    let cons : ('a * 'a mstate, 'a) m =
        function
        | [] -> Error "Cannot cons from the empty list."
        | x::xs -> Ok ((x, xs), xs)

    (* drop function for lists *)
    let rec drop n : (unit, 'b) m = fun l -> 
        match Int.compare n 0 with
        | -1 -> Error "Drop negative"
        | 0 -> Ok ((), l)
        | 1 -> 
            (match l with
             | [] -> Error "No more elements"
             | x::xs -> 
                runState xs @@
                let+ _ = drop (n-1) in
                return_both ())
        | _ -> Error "drop impossible"
 
    (* countSymbol is a CPS function that counts the number of times that a
     * symbol appears in the prefix of a list, and calls sc on that number and
     * the remainder of the list. *)
    let rec count_symbol (target : 'a) : (int, 'a) m =
        function
        | [] -> Ok (0, [])
        | x::xs -> if x = target then 
                            runState (x::xs) @@                        
                            let+ n = count_symbol target in
                            let+ s = get in
                            return_both @@ n + 1
                                 else Ok (0, x::xs)

    (* find_symbol is a CPS function that finds the first occurrence of some
     * character in a list, then returns the list to the left of it, inclusive on
     * the symbol, as well as the list to the right of the symbol *)
    let rec find_symbol (target : 'a) : ('a list, 'a) m =
        function
        | [] -> Error "could not find symbol."
        | x::xs -> if x = target then Ok ([x], xs)
                                 else
                        runState (xs) @@
                        let+ pre = find_symbol target in
                        return_both (x::pre)

    let rec find_end (left, right) : ('a list, 'a) m = 
        let rec find_end' l n acc = match (l, n) with
                (_, 0) -> Ok (List.rev acc, l)
              | ([], n) -> Error "could not find pair"
              | (x::xs, n) -> (match (x = right, x = left) with
                    (true, _) -> find_end' xs (n - 1) (x::acc)
                  | (_, true) -> find_end' xs (n + 1) (x::acc)
                  | _ -> find_end' xs n (x::acc)) in
        fun l ->
            find_end' l 1 []

    let rec get_pair (left, right) : ('a list, 'a) m = 
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
        fun l ->
        get_pair' l 0 false []


  end

module StateMonad =
  struct
      type ('v, 'a) m = 'a -> ('v * 'a)
      let return (x : 'v) : ('v, 'a) m = fun s -> (x, s)
      let get : ('a, 'a) m = fun s -> (s, s)
      let put (s : 'a) : (unit, 'a) m = fun s -> ((), s)
      let bind (x : ('v, 'a) m) (f : 'v -> ('b, 'a) m) : ('b, 'a) m =
          fun initState ->
              let (res, newState) = x initState in
              let newComputation = f res in
              newComputation newState
      let (>>=) = bind
      let (let-) = bind

      let return_both (x : 'v) : ('v * 'a, 'a) m = fun s -> ((x, s), s)
      let runState (s : 'a) (p : ('v, 'a) m) : 'v = fst (p s)

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

    let rec dict_to_list (d : 'a StrMap.t) =
        let seq = StrMap.to_seq d in
        Seq.fold_left (fun a b -> b::a) [] seq

    let str_dict (f : 'a -> string) (d : 'a StrMap.t) =
        let d = dict_to_list d in
        let post = List.fold_right (fun (k, v) acc ->
            (Printf.sprintf "%s: %s, " k (f v)) ^ acc)
            d "}" in 
        "{" ^ post

    let take_two (l : 'a list) = match l with
        x::y::xs -> (x, y)
      | _ -> failwith "Unable to take two from this list."

    let reset_color () = print_string "\027[0m"

    let print_purple (s : string) = 
        let () = print_string "\027[95m" in
        let () = print_string s in
        reset_color ()

    let print_blue (s : string) = 
        let () = print_string "\027[94m" in 
        let () = print_string s in 
        print_string "\027[0m"
  
    let print_red (s : string) =
        let () = print_string "\027[91m" in
        let () = print_string s in
        reset_color ()

    let print_yellow (s : string) =
        let () = print_string "\027[93m" in
        let () = print_string s in
        reset_color ()

    let rec zip (l : 'a list) (r : 'b list) : ('a * 'b) list =
        match (l, r) with
        | ([], _) -> []
        | (_, []) -> []
        | (x::xs, y::ys) -> (x, y) :: (zip xs ys)

    let list_to_str (f : 'a -> string) (l : 'a list) =
        let mapped = List.map f l in
        List.fold_left (fun elem acc -> elem ^ " " ^ acc) "" mapped
    
    let print_list (f : 'a -> string) (l : 'a list) =
        let s = list_to_str f l in
        let _ = print_string s in
        let _ = print_string "\n" in
        ()

    let print_opt (f : 'a -> string) (o : 'a option) =
        match o with
        | None -> "NONE"
        | Some v -> f v 
  end
