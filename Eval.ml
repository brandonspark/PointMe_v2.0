#use "Parser.ml";;

type var = 
    { name : string;
      ty   : ty;
      data : obj option;
      scope : int
    }

type heap_block = HeapRef of int * obj ref
                | HeapArray of int * obj Array.t

(* convention: before then after *)
type assign = VarAsgn of var option * var
            | Clear of var StrMap.t * var StrMap.t
            | MutObj of (int * obj ref) * obj * obj
            | MutArray of (int * obj Array.t) * int * obj * obj
            | AllocHeap of heap_block
            | ScopeChange of int
type state = 
    { prev  : (line * assign list) list;   (* list of previous lines + what they did *)
      next  : (line * assign list) list;   (* list of next lines + what they do *)
      stack : var StrMap.t;                (* map keeping stack data *)
      scope : int;
      heap  : heap_block list;             (* map keeping heap data *)
      asgns : line * assign list           (* current assigns *)
    }

module type EVAL =
  sig
    type ('a, 'b) delay
    val eval_program : string -> (obj, state) delay res
    val run : string -> obj
    val get_stack : (obj, state) delay res -> (string * var) list
    val next : ('a, state) delay res -> ('a, state) delay res 
    val recurse : ('a, 'b) delay res -> ('a * 'b -> ('c, 'b) delay res) -> ('c, 'b) delay res 
  end

let str_var (v : var) =
    Printf.sprintf "<name: %s, type: %s, obj: %s, scope: %d>" 
    v.name (str_ty v.ty) 
    (match v.data with
    | Some obj -> str_obj obj
    | None -> "NONE") v.scope

let str_assign (a : assign) = 
    match a with
    | VarAsgn (prev_opt, post) ->
        Printf.sprintf "Assign: %s -> %s" (Utils.print_opt str_var prev_opt) (str_var post)
    | Clear (prev, post) ->
        Printf.sprintf "Clear: %s -> %s" 
        (Utils.str_dict str_var prev) (Utils.str_dict str_var post)
    | MutObj ((i, cell), prev, post) ->
        Printf.sprintf "(REF %d): %s -> %s"
        i (str_obj prev) (str_obj post)
    | MutArray ((i, arr), index, prev, post) ->
        Printf.sprintf "(ARR %d)[%d]: %s -> %s"
        i index (str_obj prev) (str_obj post)
    | AllocHeap (HeapRef (i, cell)) ->
        Printf.sprintf "ALLOC: %d" i
    | AllocHeap (HeapArray (i, arr)) ->
        Printf.sprintf "ALLOC_ARRAY: %d" i


module Eval : EVAL = 
  struct
    open ResultMonad
    open ListStateResMonad
    open Pratt

    (****************************************************
     * Store of helper functions for BinOp purposes.    *
     ****************************************************)

    let lshift (x : Int32.t) (y : Int32.t) =
        Int32.shift_left x (Int32.to_int y)

    let rshift (x : Int32.t) (y : Int32.t) =
        Int32.shift_right x (Int32.to_int y)
    
    let leq x y = Int32.compare x y <> 1
    let geq x y = Int32.compare x y <> -1
    let lt x y = Int32.compare x y = -1
    let gt x y = Int32.compare x y = 1
    
    let arith_binops = [Plus, Int32.add;
                        Asterisk, Int32.mul;
                        Minus, Int32.sub;
                        Slash, Int32.div;
                        Percent, Int32.rem;
                        LShift, lshift;
                        RShift, rshift;
                        Amper, Int32.logand;
                        Caret, Int32.logxor;
                        Pipe, Int32.logor]

    let comp_binops = [Leq, leq;
                       Geq, geq;
                       LChevron, lt;
                       RChevron, gt]

    let bool_binops = [And, (&&);
                       Or, (||)]

   (****************************************************
    * Some helpful declarations.                       *
    ****************************************************)

   let init_state = 
        { prev = [];
          next = [];
          stack = StrMap.empty;
          scope = 0;
          heap = [];
          asgns = ([], []);}

    exception InvalidState of state 
    exception InvalidToken of token list
    let raiseState state = raise (InvalidState state)

    (* 'a is the type of the return of the entire computation -
     * 'b is the type of the "evidence" that the computation returns as it proceeds *)
    type ('a, 'b) delay = Done of ('a * 'b)
                        | Comp of 'b * (unit -> ('a, 'b) delay res)
    
    type direction = Index of Int32.t
                   | Deref
                   | Field of string
                   | VarName of string
    
    (* lets you chain together different delays, to make them compose their
     * answers *)
    let rec recurse (x : ('a, 'b) delay res) 
                    (f : 'a * 'b -> ('c, 'b) delay res) : ('c, 'b) delay res= 
        ResultMonad.(>>=) x (fun d ->
            (match d with
            | Done (res, new_state) -> f (res, new_state)
            | Comp (s, g) ->
                Ok (Comp (s, fun () -> 
                    let next = g () in 
                    (match next with
                    | Ok delay -> recurse next f
                    | Error e -> Error e)))))

   (****************************************************
    * Helper functions for eval_program.               *
    ****************************************************)

    let add_asgn (a : assign) (s : state) = 
        let (line, asgnlist) = s.asgns in
        {s with asgns = (line, a::asgnlist)}
    
    let add_var (v : var) (s : state) =
        let {name=name; _} = v in
        {s with stack = StrMap.add name v s.stack}

    let add_block (h : heap_block) (s : state) =
        {s with heap = h::s.heap}

    let remove_block (h : heap_block) (s : state) =
        if not (List.memq h s.heap) then
            failwith "Removing a heap block that doesn't exist."
        else
            let new_heap = List.filter (fun elem -> elem != h) s.heap in
            {s with heap = new_heap}

    let exp_from_line (line : line) =
        runState line @@
        let+ res = Pratt.expr_bp 0 in
        return res

    let rec find_var (id : string) (s : state) =
        try Some (StrMap.find id s.stack)
        with Not_found -> None 

    (* instantiate a new variable to the state. *)
    let rec init_var (t: ty) (id : string) 
                    (o : obj option) (s : state) : state res =
        match find_var id s with
        | Some old_var -> Error "Attempting to initialize already initialized var."
        | None ->
            let var = {name = id; ty = t; data = o; scope = s.scope} in
            let added_stack = StrMap.add id var s.stack in
            let new_state = add_asgn (VarAsgn (None, var)) s in
            Ok {new_state with stack = added_stack}

    let upscope (s : state) : state =
        {s with scope = s.scope + 1}

    let get_var_scope (v : var) = v.scope

    let rec descope (s : state) : state =
        let new_s = {s with scope = s.scope - 1} in
        let new_stack = StrMap.filter (fun k elem -> (get_var_scope elem) <= new_s.scope) new_s.stack in 
        {new_s with stack = new_stack}

    let refocus (s : state) (l : line) : state =
        {s with prev = s.asgns::s.prev; asgns = (l, [])}

    let replace_stack (new_stack : var StrMap.t) (old_state : state) =
        let old_stack = old_state.stack in
        let added_asgn = add_asgn (Clear (old_stack, new_stack)) old_state in
        let new_state = {added_asgn with stack = new_stack} in
        new_state

    let rec repeat (s : string) = function
        | 0 -> ""
        | n -> s ^ (repeat s (n - 1))

    let indent = "    " 

    let str_assignlist (line, l) =
        (Utils.list_to_str str_token line, List.map (fun x -> indent ^ (str_assign x)) l)

    let str_heapblock (h : heap_block) =
        match h with
        | HeapRef (i, _) -> Printf.sprintf "(REF %d)" i
        | HeapArray (i, arr) -> Printf.sprintf "(ARR %d)[%d]" i (Array.length arr)

    let print_state (s : state) = 
        let _ = Sys.command "clear" in
        let equal_line () = Utils.print_red @@ (repeat "=" 40 ^ "\n") in
        let thin_line = (repeat "-" 20 ^ "\n") in
        let print_str_strlist ((s : string), (ss : string list)) = 
            let _ =  
                (match s with
                | "" -> Utils.print_purple "<no line>\n" 
                | _ -> Utils.print_purple (s ^ "\n")) in
            let _ = 
                match ss with
                | [] -> print_string "\n"
                | _ -> List.fold_left (fun acc elem -> print_string (elem ^ "\n\n")) () ss in
            () in

        let _ = equal_line () in

        (* Here do the current line being evaluated. *)
        let (line, _) = s.asgns in
        let _ = Utils.print_blue (Utils.list_to_str str_token line ^ "\n") in

        let _ = equal_line () in
        
        (* Here do the current scope of the program. *)
        let _ = print_string @@ (Printf.sprintf "CURRENT SCOPE: %d\n" s.scope) in
        
        let _ = equal_line () in

        (* Here do the prev assigns. *)
        let prev_num = List.length s.prev in
        let _ = print_string @@ thin_line ^ (Printf.sprintf "PREV ASSIGNS (%d):\n" prev_num) ^ thin_line in
        let rec prev_list (prev : (line * assign list) list) (n : int) =
            if n >= 5 then []
            else
                match prev with
                | [] -> []
                | x::xs -> prev_list xs (n + 1) @ [str_assignlist x] in
        let _ = List.fold_left (fun acc elem -> print_str_strlist elem) () (prev_list s.prev 0) in
        
        let _ = equal_line () in
        
        (* Here do the current assigns. *)
        let _ = print_string @@ thin_line ^ "CURRENT ASSIGNS:\n" ^ thin_line in 
        let (line, asgns) = s.asgns in
        let _ = Utils.print_purple (Utils.list_to_str str_token line ^ "\n") in
        let _ = Utils.print_list (fun x -> x) (List.map (fun x -> indent ^ (str_assign x)) asgns) in 
        
        let _ = equal_line () in

        (* Here do the next assigns. *)
        let next_num = List.length s.next in
        let _ = print_string @@ thin_line ^ (Printf.sprintf "NEXT ASSIGNS (%d):\n" next_num) ^ thin_line in
        let rec next_list (next : (line * assign list) list) (n : int) =
            if n >= 5 then []
            else
                match next with
                | [] -> []
                | x::xs -> (str_assignlist x) :: next_list xs (n + 1) in
        let _ = List.fold_left (fun acc elem -> print_str_strlist elem) () (next_list s.next 0) in
        
        let _ = equal_line () in

        (* Here do the stack. *)
        let _ = print_string @@ thin_line ^ "STACK:\n" ^ thin_line in 
        let _ = List.fold_left (fun acc (s, v) ->
            print_string (indent ^ str_var v ^ "\n")) () (Utils.dict_to_list
            s.stack) in
        let _ = equal_line () in

        (* Here do the heap. *)
        let _ = print_string @@ thin_line ^ "HEAP:\n" ^ thin_line in
        let _ = Utils.print_list str_heapblock s.heap in
        
        let _ = equal_line () in
        ()


    (****************************************************
     * The eval_program function - this is the big one. *
     ****************************************************)

    let rec eval_program (filename : string) : (obj, state) delay res =
        let* (ts, tdict, tlist, sinfo) = Lexer.lex filename in
        let* funcmap = Parser.gen_function_pool ts in
        let block_count = ref 0 in

        let typecheck_p (b : bool) =
            if b then Ok ()
                 else Error "failed to typecheck" in

        (* checks if the obj really fits the type of t *)
        let rec typecheck (t : ty) (o : obj) =
            let reduce_t = fun t -> Lexer.reduce_type t tlist tdict in
            let* redtype = reduce_t t in
            match (redtype, o) with
            | (Base "char", CharObj _)
            | (Base "int", IntObj _)
            | (Base "string", StrObj _)
            | (Base "bool", BoolObj _)
            | (Base "void", VoidObj) -> Ok ()
            | (Base stype_name, StructObj (t, args)) ->
                let* new_t = reduce_t t in 
                if redtype <> new_t
                    then Error "Failed to typecheck."
                    else let fields : (ty * string) list = StrMap.find stype_name sinfo in
                         args_typecheck fields args
            | (Ptr t', PtrObj (ptr_t, ptr_opt)) -> 
                let* new_t = reduce_t ptr_t in
                if t' <> new_t
                    then Error "failed to typecheck"
                    else 
                        (match ptr_opt with
                        | Some (_, ptr_ref) -> typecheck t' (!ptr_ref)
                        | None -> Ok ())
            | (Array t', ArrObj (arr_t, arr_opt)) -> 
                let* new_t = reduce_t arr_t in
                if t' <> new_t
                    then Error "failed to typecheck"
                    else 
                        (match arr_opt with
                        | None -> Ok ()
                        | Some (_, arr) ->
                            typecheck_p @@ (Array.fold_left
                            (fun acc b -> b && acc) true
                            (Array.map (fun obj -> 
                                    Ok () = typecheck t' obj
                            ) arr)))
            | _ -> Error "Failed to typecheck" 
        
        and args_typecheck (fields : (ty * string) list) 
                           (args : obj StrMap.t) =
            typecheck_p @@ (List.fold_left
            (fun acc (t, name) ->
                let res_obj = StrMap.find name args in
                acc && (Ok () = typecheck t res_obj)
            ) true fields) in    
        
        let rec base_obj (t : ty) : obj res =
            let* new_t = Lexer.reduce_type t tlist tdict in
            match new_t with
            | Base "int" -> Ok (IntObj (Int32.of_int 0))
            | Base "string" -> Ok (StrObj "")
            | Base "char" -> Ok (CharObj '\x00')
            | Base "bool" -> Ok (BoolObj false)
            | Base "void" -> Ok (VoidObj)
            | Base name -> 
                (try let info = StrMap.find name sinfo in
                    let fold_res = List.fold_left (fun dict_res (s_t, field) ->
                        let* dict = dict_res in 
                        let* field_obj = base_obj s_t in
                        Ok (StrMap.add field field_obj dict)) (Ok StrMap.empty) info in
                    (match fold_res with
                    | Ok dict -> Ok (StructObj (t, dict))
                    | Error e -> Error e)
                with Not_found -> Error "Name of base obj not recognized.")
            | Ptr t' -> Ok (PtrObj (t', None))
            | Array t' -> Ok (ArrObj(t', None)) in
                    
        (* get_directions evaluates the given AST *)
        let rec get_directions (ast : ast) (s : state) 
                           (acc : direction list) : (direction list, state) delay res =
            match ast with
            | UnOp (Asterisk, hole) ->
                get_directions hole s (Deref::acc)
            | DotAccess (hole, field) ->
                get_directions hole s ((Field field)::acc)
            | ArrayAccess (hole, expr) ->
                recurse (eval_exp expr s) (fun (obj, new_state) ->
                    (match obj with
                    | IntObj i ->
                        get_directions hole new_state ((Index i)::acc)
                    | _ -> Error "Indexed with a non-IntObj."))
            | ArrowAccess (hole, field) -> 
                get_directions hole s (Deref :: (Field field) :: acc)
            | Name name -> Ok (Done ((VarName name)::acc, s))
            | _ -> Error "not a valid lvalue AST."

        (* for assignment operators like += *)
        and assign_ast (dl : direction list) (op : token) 
                       (s : state) (r_ast : Pratt.ast) : (unit, state) delay res =
            recurse (eval_exp r_ast s) (fun (rhs_obj, new_state) ->
                let* assigned_state = 
                    follow dl new_state (fun follow_res ->
                        match follow_res with
                        | Some followed_obj ->
                                (try let (_, f) = List.find (fun (t, _) -> t = op) arith_binops in 
                                    (match (followed_obj, rhs_obj) with
                                    | (IntObj i1, IntObj i2) -> Ok (IntObj (f i1 i2))
                                    | _ -> Error "Received non-IntObjs with an assign op.")
                                with Not_found -> Error "assign_ast on invalid op.")
                        | _ -> Error "Attempting assignment op on None obj.") in
                Ok (Done ((), assigned_state)))
        
        (* follow should let you take the directions corresponding to an l-value
         * and then change the state to reflect the assignment to new_obj 
         * *)
        and follow (dl : direction list) (s : state) (obj_fun : obj option -> obj res) : state res =
            match dl with
            | (VarName name)::rest ->
                
                let rec follow' (dl : direction list) 
                                (hole : obj option) (s : state) : (obj * state) res =
                    (match (dl, hole) with
                    | ([], _) -> 
                        let* v = obj_fun hole in
                        Ok (v, s)
                    | (_, None) -> Error "Tried to follow directions into a None
                    object."
                    | ((Index i)::xs, Some hole_obj) ->
                        (match hole_obj with
                        | ArrObj (t, arr_opt) -> 
                            (match arr_opt with
                            | None -> Error "Indexing into unallocated array."
                            | Some (count, arr) ->
                                let old_arr_elem = Array.get arr (Int32.to_int i) in 
                                let* (new_arr_elem, new_state) = follow' xs (Some old_arr_elem) s in
                                let _ = Array.set arr (Int32.to_int i) (new_arr_elem) in
                                let asgn_state = add_asgn 
                                    (MutArray ((count, arr), Int32.to_int i, 
                                               old_arr_elem, new_arr_elem)) new_state in
                                Ok (ArrObj (t, arr_opt), asgn_state))
                        | _ -> Error "Got an index with a non-Array object.")
                    
                    | (Deref::xs, Some hole_obj) ->
                        (match hole_obj with 
                        | PtrObj (t, ptr_opt) ->
                            (match ptr_opt with
                            | Some (i, ptr_ref) ->
                                let old_ptr_elem = !ptr_ref in 
                                let* (new_ptr_elem, new_state) = follow' xs (Some old_ptr_elem) s in
                                let _ = ptr_ref := new_ptr_elem in
                                let asgn_state = add_asgn 
                                (MutObj ((i, ptr_ref), old_ptr_elem, new_ptr_elem)) new_state in
                                Ok (PtrObj (t, ptr_opt), asgn_state)
                            | _ -> Error "Dereferencing unallocated pointer.")
                        | _ -> Error "Got a Deref with a non-Ptr object.")
                    
                    | ((Field name)::xs, Some hole_obj) ->
                        (match hole_obj with
                        | StructObj (t, struct_map) ->
                            let old_struct_elem = StrMap.find name struct_map in
                            let* (new_struct_elem, new_state) = follow' xs (Some old_struct_elem) s in
                            let new_struct_map = StrMap.add name new_struct_elem struct_map in
                            Ok (StructObj (t, new_struct_map), s)
                        | _ -> Error "Got a Field with a non-Struct object.")
                    | _ -> Error "Should not be possible") in 


                let* (old_obj, t, old_scope) = 
                    (try let {name=name; ty=t; data=o; scope=old_scope} = StrMap.find name s.stack in
                        Ok (o, t, old_scope)
                    with Not_found -> Error "Old var not found.") in
                let old_var = find_var name s in
                let* (new_obj, new_state) = follow' rest old_obj s in
                let new_var = {name=name; ty=t; data= Some new_obj; scope=old_scope} in
                let updated_state = {new_state with 
                    stack = StrMap.add name new_var new_state.stack} in
                let updated_state2 = add_asgn (VarAsgn (old_var, new_var)) updated_state in
                Ok updated_state2
            | _ -> failwith "Impossible."
        
        and eval_line (line : token list) (s : state) : (unit, state) delay res = 
            match line with
            | (Type t)::(Identifier vid)::rest ->
                (match rest with 
                | [Semicolon] -> 
                    let* new_state = init_var t vid None s in
                    Ok (Done ((), new_state))
                | (Equal None)::rest -> (* <ty> <id> = <something> *)
                    let* rhs_ast =  
                        (runState rest @@
                        let+ rhs = Pratt.expr_bp 0 in
                        return rhs) in
                    let rhs_delay = eval_exp rhs_ast s in
                    recurse rhs_delay (fun (rhs_obj, new_state) ->
                        let* updated_state = init_var t vid (Some rhs_obj) new_state in
                        Ok (Done ((), updated_state)))
                | _ -> Error "Invalid pattern after <ty> <id>")
            | _ -> 
                let* (l_ast, rest) = 
                    (runState line @@
                    let+ ast = Pratt.expr_bp 0 in
                    return_both ast) in
                (match rest with
                | [Semicolon] -> 
                    recurse (eval_exp l_ast s) (fun (exp_obj, new_state) ->
                        Ok (Done ((), new_state)))
                | _ ->
                    let dir_delay = get_directions l_ast s [] in

                    (match rest with
                    | [Increment; Semicolon] ->
                        recurse dir_delay (fun (directions, new_state) ->
                            let* assigned_state = 
                                follow directions new_state (fun follow_res ->
                                    (match follow_res with
                                    | Some (IntObj i) -> Ok (IntObj (Int32.add i Int32.one))
                                    | _ -> Error "Follow returned non-Int object.")) in
                            Ok (Done ((), assigned_state)))
                    | [Decrement; Semicolon] ->
                        recurse dir_delay (fun (directions, new_state) ->
                            let* assigned_state = 
                                follow directions new_state (fun follow_res ->
                                    (match follow_res with
                                    | Some (IntObj i) -> Ok (IntObj (Int32.sub i Int32.one))
                                    | _ -> Error "Follow returned non-Int object.")) in
                            Ok (Done ((), assigned_state)))
                    | (Equal op)::rest' ->
                        let* rhs_ast =
                            (runState rest' @@
                            let+ rhs = Pratt.expr_bp 0 in
                            return rhs) in
                        (match op with
                        | Some op' ->
                            recurse (dir_delay) (fun (directions, new_state) ->
                            recurse (assign_ast directions op' new_state rhs_ast) 
                            (fun (_, after_state) ->
                            Ok (Done ((), after_state))))

                        | None ->
                            recurse dir_delay (fun (directions, new_state) ->
                            recurse (eval_exp rhs_ast new_state) (fun (rhs_obj, rhs_state) ->
                             
                            let* followed_state = follow directions new_state (fun _ -> Ok rhs_obj) in
                            Ok (Done ((), followed_state))
                            )))
                    | _ -> Error "Invalid syntax after l-value."))

        

        and eval_for (line : token list) (ast : statement) (s : state) =
            let* (init, guard, step) = 
                runState line @@
                let+ _ = ListStateResMonad.find_symbol LParen in
                let+ init = ListStateResMonad.find_symbol Semicolon in
                let+ guard = ListStateResMonad.find_symbol Semicolon in
                let+ step = get in
                let step = Utils.take step (List.length step - 1) in
                return (init, guard, step) in
            let* guard_exp = 
                runState guard @@
                let+ v = Pratt.expr_bp 0 in
                return v in
            let rec run_for (s : state) : (obj option, state) delay res =
                let refocus_s = refocus s guard in
                Ok (Comp (refocus_s, fun () ->
                recurse (eval_exp guard_exp refocus_s) (fun (guard_obj, guarded_state) ->
                match guard_obj with
                | BoolObj b -> 
                    if b then 
                        let up_state = upscope guarded_state in
                        recurse (eval_statement ast up_state) (fun (eval_opt, after_state) ->
                            (match eval_opt with
                            | Some eval_obj ->
                                let down_state = descope after_state in
                                Ok (Done (Some eval_obj, down_state))
                            | _ ->
                                let down_state = descope after_state in
                                let refocus_s = refocus down_state (step @ [Semicolon]) in
                                Ok (Comp (refocus_s, fun () ->
                                recurse (eval_line (step @ [Semicolon]) refocus_s) (fun ((), step_state) ->
                                run_for step_state)))))
                    else 
                        let down_state = descope guarded_state in
                        Ok (Done (None, down_state))
                | _ -> Error "Guard returned a non-bool."))) in

            let new_state = upscope s in   
            let refocus_s = refocus new_state init in
            Ok (Comp (refocus_s, fun () ->
            recurse (eval_line init refocus_s) (fun (_, after_state) ->
                run_for after_state)))

        and eval_while (line : token list) (ast : statement) (s : state) =
            let* guard_exp =
                runState line @@
                let+ _ = ListStateResMonad.find_symbol LParen in
                let+ v = Pratt.expr_bp 0 in
                return v in
            let up_state = upscope s in
            let rec run_while (s : state) : (obj option, state) delay res =
                recurse (eval_exp guard_exp s) (fun (guard_obj, guarded_state) ->
                    match guard_obj with
                    | BoolObj b ->
                        if b then
                            recurse (eval_statement ast guarded_state) (fun (eval_opt, after_state) ->
                                (match eval_opt with
                                | Some eval_obj ->
                                    let down_state = descope after_state in
                                    Ok (Done (Some eval_obj, down_state))
                                | _ -> 
                                    run_while after_state))
                        else
                            let down_state = descope guarded_state in
                            Ok (Done (None, down_state))
                    | _ -> Error "Guard returned a non-bool.") in
            run_while up_state
                
        and eval_if (cond : token list) (if_ast : statement) 
                        (else_ast_opt : statement option) (s : state) =
            let* cond_exp = 
                runState cond @@
                let+ _ = ListStateResMonad.find_symbol LParen in
                let+ v = Pratt.expr_bp 0 in 
                return v in
            let refocus_s = refocus s cond in
            Ok (Comp (refocus_s, fun () ->
            recurse (eval_exp cond_exp refocus_s) (fun (cond_obj, cond_state) ->
                match cond_obj with
                | BoolObj b ->
                    if b then
                        let up_state = upscope cond_state in
                        recurse (eval_statement if_ast up_state) (fun (eval_opt, if_state) ->
                            let down_state = descope if_state in
                            Ok (Done (eval_opt, down_state)))
                    else
                        (match else_ast_opt with
                        | Some else_ast ->
                            let up_state = upscope cond_state in
                            recurse (eval_statement else_ast up_state) (fun (eval_opt, else_state) ->
                                (* this too *)
                                (match eval_opt with
                                | Some eval_obj -> 
                                    let down_state = descope else_state in
                                    Ok (Done (Some eval_obj, down_state))
                                | _ -> 
                                    let down_state = descope else_state in
                                    Ok (Done (None, down_state))))
                        | None -> Ok (Done (None, cond_state)))
                | _ -> Error "Cond returned a non-bool.")))
                    
        and eval_block (l : statement list) (s : state) =
            match l with
            | [] -> 
                let down_state = descope s in
                Ok (Done (None, down_state))
            | x::xs ->
                recurse (eval_statement x s) (fun (stmt_opt, stmt_state) ->
                (match stmt_opt with
                | Some ret -> Ok (Done (Some ret, stmt_state))
                | None ->
                    eval_block xs stmt_state)) 

        (* when you evaluate a statement, return a continuation to the next
         * thing (and the previous thing), and update the state *)
        (* this is where side effects happen. *)
        and eval_statement (ast : statement)
                               (s: state) : (obj option, state) delay res = 
            match ast with
            | SimpleStmt line ->
                let refocus_s = refocus s line in
                Ok (Comp (refocus_s, fun () ->
                recurse (eval_line line refocus_s) (fun ((), line_state) ->
                    Ok (Done (None, line_state)))))
            | IfStmt (cond, code, el) -> eval_if cond code el s
            | WhileStmt (cond, code) -> eval_while cond code s
            | ForStmt (line, code) -> eval_for line code s
            | BlockStmt l ->
                let up_state = upscope s in
                eval_block l up_state
            | ReturnStmt line ->
                let refocus_s = refocus s (Return::line) in
                Ok (Comp (refocus_s, fun () ->
                let* line_exp = exp_from_line line in 
                recurse (eval_exp line_exp refocus_s) (fun (eval_obj, eval_state) ->
                Ok (Done (Some eval_obj, eval_state)))))
            | AssertStmt line ->
                let refocus_s = refocus s (Assert::line) in
                Ok (Comp (refocus_s, fun () ->
                let* line_exp = exp_from_line line in
                recurse (eval_exp line_exp refocus_s) (fun (eval_obj, eval_state) ->
                (match eval_obj with
                | BoolObj b ->
                    if b then 
                        Ok (Done (None, eval_state))
                    else
                        Error "Assert failed."
                | _ -> Error "Non-bool given to Assert."))))
            | ErrorStmt line ->
                let refocus_s = refocus s (Error_t::line) in
                Ok (Comp (refocus_s, fun () ->
                let* line_exp = exp_from_line line in 
                recurse (eval_exp line_exp refocus_s) (fun (eval_obj, eval_state) ->
                (match eval_obj with
                | StrObj s ->
                    Error (Printf.sprintf "Program Error: %s" s)
                | _ -> Error "Non-string given to Error."))))
            
        and eval_function (s : string) (state : state) (arglist: (ty * string * obj) list) =
            try (let func_info = StrMap.find s funcmap in
                let old_stack = state.stack in
                let old_scope = state.scope in
                let reset_state = {state with scope = 0} in
                let new_stack =
                    List.fold_left (fun acc (t, name, o) ->
                        StrMap.add name {name = name; ty = t; data = Some o; scope = 1} acc)
                        StrMap.empty arglist in
                let populated_state = replace_stack new_stack reset_state in
                recurse (eval_statement func_info.ast populated_state) (fun (eval_opt, eval_state) ->
                    let new_state = replace_stack old_stack eval_state in
                    let reset_state = {new_state with scope = old_scope} in
                    (match eval_opt with
                    | Some eval_obj ->
                        Ok (Done (eval_obj, reset_state))
                    | None ->
                        Ok (Done (VoidObj, reset_state)))))
            with Not_found -> Error "Failed to find function."

        and eval_eq (l : obj) (r: obj) : bool =
            match (l, r) with
            | (IntObj i1, IntObj i2) -> i1 = i2
            | (CharObj c1, CharObj c2) -> c1 = c2 
            | (StrObj s1, StrObj s2) -> s1 = s2 
            | (BoolObj b1, BoolObj b2) -> b1 = b2 
            | (VoidObj, VoidObj) -> true
            | (StructObj (t1, s1), StructObj (t2, s2)) ->
                let reduce_t1 = Lexer.reduce_type t1 tlist tdict in
                let reduce_t2 = Lexer.reduce_type t2 tlist tdict in
                (match (reduce_t1, reduce_t2) with
                | (Ok ty_1, Ok ty_2) ->
                    if ty_1 <> ty_2 then false
                    else
                    StrMap.equal (fun v1 v2 -> eval_eq v1 v2)
                    s1 s2
                | _ -> false)
            | (PtrObj (_, p1), PtrObj (_, p2)) ->
                (match (p1, p2) with
                | (Some p1, Some p2) -> p1 == p2
                | _ -> false)
            | (ArrObj (_, a1), ArrObj (_, a2)) ->
                (match (a1, a2) with
                | (Some a1, Some a2) -> a1 == a2
                | _ -> false)
            | _ -> false

        and eval_exp (ast : Pratt.ast) (s : state) : (obj, state) delay res = 
            match ast with
            | BinOp (op, lhs, rhs) ->
                recurse (eval_exp lhs s) (fun (lhs_res, s') ->
                recurse (eval_exp rhs s') (fun (rhs_res, s'') ->
                (match op with
                | EqEq ->
                    if eval_eq lhs_res rhs_res then Ok (Done (BoolObj true, s''))
                    else Ok (Done (BoolObj false, s''))
                | _ ->
                (try (let (_, f) = List.find (fun (t, _) -> t = op) arith_binops in
                    (match (lhs_res, rhs_res) with
                    | (IntObj i1, IntObj i2) -> Ok (Done (IntObj (f i1 i2), s''))
                    | _ -> Error "Did not get IntObj for int BinOps.")
                    )
                with Not_found ->
                    (try (let (_, f) = List.find (fun (t, _) -> t = op) comp_binops in
                        match (lhs_res, rhs_res) with
                        | (IntObj i1, IntObj i2) -> Ok (Done (BoolObj (f i1 i2), s''))
                        | _ -> Error "Did not get IntObjs for comp BinOps."
                        )
                    with Not_found ->
                    (try (let (_, f) = List.find (fun (t, _) -> t = op) bool_binops in
                        match (lhs_res, rhs_res) with
                        | (BoolObj b1, BoolObj b2) -> Ok (Done (BoolObj (f b1 b2), s''))
                        | _ -> Error "Did not get BoolObj for bool BinOps."
                        )
                    with Not_found -> Error "Invalid op for BinOp."))))))
            | UnOp (op, arg) ->
                recurse (eval_exp arg s) (fun (res, new_state) ->
                    (match (op, res) with
                    | (Bang, BoolObj b) -> Ok (Done (BoolObj (not b), new_state))
                    | (Tilde, IntObj i) -> Ok (Done (IntObj (Int32.lognot i), new_state))
                    | (Minus, IntObj i) -> Ok (Done (IntObj (Int32.neg i), new_state))
                    | (Asterisk, PtrObj (t, ptr_opt)) ->
                        (match ptr_opt with
                        | Some (_, ptr_ref) ->
                            Ok (Done (!ptr_ref, new_state))
                        | None -> Error "Tried to access unallocated pointer")
                    | _ -> Error "Invalid op/type for UnOp."))
            | Call (name, arglist) -> 
                (try let func = StrMap.find name funcmap in
                    if List.length arglist <> List.length func.args then
                        Error "Invalid number of arguments for function."
                    else 
                        let zipped = Utils.zip arglist func.args in 
                        let before_call = 
                        List.fold_left (fun acc (arg_exp, (t, field)) -> 
                            recurse acc (fun (l, acc_state) ->
                            recurse (eval_exp arg_exp acc_state) (fun (eval_obj, eval_state) ->
                            let* _ = typecheck t eval_obj in
                            Ok (Done ((t, field, eval_obj)::l, eval_state)))))
                        (Ok (Done ([], s))) zipped in
                        recurse before_call (fun (objlist, args_state) ->
                        recurse (eval_function name args_state objlist) (fun (ret_obj, func_state) ->
                        Ok (Done (ret_obj, func_state))))
                with Not_found ->
                    Error "Tried to use nonexistent function.")
            | Name name ->
                (try let var = StrMap.find name s.stack in
                    (match var.data with
                    | Some obj ->
                        Ok (Done (obj, s))
                    | None ->
                        Error "Tried to use value of uninitialized var.")
                with Not_found ->
                    raise (InvalidState s)
                    (*Error "Tried to look up variable that did not exist."*))
            | Lit obj -> Ok (Done (obj, s))
            | DotAccess (ast, field) ->
                recurse (eval_exp ast s) (fun (eval_obj, eval_state) ->
                    (match eval_obj with
                    | StructObj (t, s_map) ->
                        (try let res_obj = StrMap.find field s_map in
                            Ok (Done (res_obj, s))
                        with Not_found ->
                            Error "Field not found.")
                    | _ -> Error "Tried to access field of non-Struct object."))
            | ArrowAccess (ast, field) ->
                eval_exp (DotAccess (UnOp (Asterisk, ast), field)) s
            | ArrayAccess (ast, index_ast) ->
                recurse (eval_exp ast s) (fun (main_obj, first_state) ->
                recurse (eval_exp index_ast first_state) (fun (index_obj, after_state) ->
                    (match (main_obj, index_obj) with
                    | (ArrObj (t, arr_opt), IntObj i) ->
                        (match arr_opt with
                        | None -> Error "Indexing into unallocated array."
                        | Some (_, arr) ->
                        (try let arr_obj = Array.get arr (Int32.to_int i) in
                            Ok (Done (arr_obj, after_state))
                        with _ ->
                            Error "Index of int object out of array bounds."))
                    | _ -> Error "Not valid objects for array indexing.")))
            | Cond (cond, first, second) ->
                recurse (eval_exp cond s) (fun (cond_obj, cond_state) ->
                recurse (eval_exp first cond_state) (fun (first_obj, first_state) ->
                recurse (eval_exp second first_state) (fun (sec_obj, sec_state) ->
                    (match cond_obj with
                    | BoolObj b ->
                        if b then
                            Ok (Done (first_obj, sec_state))
                        else
                            Ok (Done (sec_obj, sec_state))
                    | _ -> Error "Cond not a BoolObj."))))
            | AllocNode t ->
                let* contents = base_obj t in
                let new_ref = ref contents in
                let count = !block_count in
                let new_obj = PtrObj (t, Some (count, new_ref)) in
                let _ = block_count := (!block_count + 1) in
                let added_state = add_asgn (AllocHeap (HeapRef (count, new_ref))) s in 
                let new_state = {added_state with
                    heap = (HeapRef (count, new_ref))::added_state.heap} in
                Ok (Done (new_obj, new_state))
            | AllocArrNode (t, ast) ->
                recurse (eval_exp ast s) (fun (size_obj, size_state) ->
                (match size_obj with
                | IntObj size ->
                    let* contents = base_obj t in
                    let new_arr = Array.make (Int32.to_int size) contents in
                    let count = !block_count in
                    let new_obj = ArrObj (t, Some (count, new_arr)) in
                    let _ = block_count := (!block_count + 1) in
                    let added_state = add_asgn (AllocHeap (HeapArray (count,
                    new_arr))) size_state in 
                    let new_state = {added_state with
                        heap = (HeapArray (count, new_arr))::added_state.heap} in
                    Ok (Done (new_obj, new_state))
                | _ -> Error "Tried to allocate array with non-int.")) in
        let res = eval_function "main" init_state [] in
        match res with
        | Ok (Done (_, s)) | Ok (Comp (s, _)) -> print_state s; res
        | _ -> res

        let eval_asgn (x : assign) (s : state) =
            let new_s = add_asgn x s in
            match x with
            | VarAsgn (pre, ({name=name; _} as post)) ->
                {new_s with stack = StrMap.add name post new_s.stack}
            | Clear (pre, post) ->
                if pre <> new_s.stack then failwith "Mismatch in stacks at Clear time."
                else 
                    {new_s with stack = post}
            | MutObj ((_, ptr), prev, post) ->
                ptr := post; s
            | MutArray ((_, arr), index, prev, post) ->
                Array.set arr index post; s
            | AllocHeap h ->
                remove_block h s 

        let prev (x : ('a, 'b) delay res) ->
            | Error e -> failwith e
            | Ok v ->
                let state = (match v with Done (_, s) -> s | Comp (s, _) -> s in
                let res = (match (state.prev, v) with
                | ([], _) -> failwith "Computation is at its beginning."
                | ((_, l)
        
        let next (x : ('a, 'b) delay res) =
            match x with
            | Error e -> failwith e
            | Ok v ->
                let state = (match v with Done (_, s) -> s | Comp (s, _) -> s) in
                let res = (match (state.next, v) with
                | ([], Done (v, s)) -> failwith "Computation done."
                | ([], Comp (state, f)) ->  f ()
                | ((_, l)::xs, Done (v, s)) ->
                    let new_state = List.fold_right (fun elem acc ->
                        eval_asgn elem acc) l s in
                    let new_new_state = {new_state with next = xs} in
                    Ok (Done (v, new_new_state))
                | ((_, l)::xs, Comp (s, f)) ->
                    let new_state = List.fold_right (fun elem acc ->
                        eval_asgn elem acc) l s in
                    let new_new_state = {new_state with next = xs} in
                    Ok (Comp (new_new_state, f))) in

                (match res with
                | Ok (Done (v, state)) ->
                    let _ = print_state state in
                    res
                | Ok (Comp (state, f)) ->  
                    let _ = print_state state in
                    res
                | Error e -> failwith e)

        let get_stack (x : ('a, state) delay res) =
            match x with
            | Ok (Done (v, s)) -> Utils.dict_to_list s.stack
            | Ok (Comp (s, f)) -> Utils.dict_to_list s.stack
            | _ -> failwith "No real thing."

        let run (s : string) =
            let delay = eval_program s in
            let rec run' (x : ('a, state) delay res) =
                match x with
                | Ok (Done (a, s)) -> a
                | Ok (Comp (s, f)) -> run' (next x) 
                | Error e -> failwith e in
            run' delay
  end
