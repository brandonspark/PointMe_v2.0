#use "Parser.ml";;

type var = 
    { name : string;
      ty   : ty;
      data : obj option;
      scope : int
    }

(* convention: before then after *)
type assign = VarAsgn of var option * var
            | Clear of var StrMap.t * var StrMap.t
            | MutObj of obj option ref * obj option * obj
            | MutArray of obj option Array.t * int * obj option * obj

module IntMap = Map.Make(Int);;

type state = 
    { prev  : (line * assign list) list;   (* list of previous lines + what they did *)
      next  : (line * assign list) list;   (* list of next lines + what they do *)
      stack : var StrMap.t;                (* map keeping stack data *)
      scope : int;
      heap  : obj ref IntMap.t;            (* map keeping heap data *)
      asgns : line * assign list           (* current assigns *)
    }

module Eval = 
  struct
    open ResultMonad
    open ListStateResMonad

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

    (*let rec eval_program (filename : string) : 'a =
        let* (ts, tdict, tlist, sinfo) = Lexer.lex filename
        let* funcmap = Parser.gen_function_pool ts*)

        (*
        let rec assign_help (t : token option) (rhs : Pratt.ast) : Pratt.ast res =
            match t with
            | Some t ->
            | Some Pipe -> Ok (BinOp (t, ast, 
            | None -> Ok ast
            | _ -> Error "Invalid token for Equal."
        *)

        let typecheck_p (b : bool) =
            if b then Ok ()
                 else Error "failed to typecheck"

        (* checks if the obj really fits the type of t *)
        let rec typecheck (t : ty) (o : obj) (tlist : string list) (tdict :
            Lexer.typeDict) sinfo =
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
                         args_typecheck fields args tlist tdict sinfo
            | (Ptr t', PtrObj (ptr_t, obj_ref)) -> 
                let* new_t = reduce_t ptr_t in
                if t' <> new_t
                    then Error "failed to typecheck"
                    else 
                        (match !obj_ref with
                        | Some obj ->
                            typecheck t' obj tlist tdict sinfo
                        | None ->
                            Ok ())
            | (Array t', ArrObj (arr_t, arr)) -> 
                let* new_t = reduce_t arr_t in
                if t' <> new_t
                    then Error "failed to typecheck"
                    else typecheck_p @@ (Array.fold_left
                         (fun acc b -> b && acc) true
                         (Array.map (fun obj_opt -> 
                            match obj_opt with
                            | Some obj ->
                                Ok () = typecheck t' obj tlist tdict sinfo
                            | None -> true) arr))
            | _ -> Error "Failed to typecheck"
        
        and args_typecheck (fields : (ty * string) list) 
                           (args : obj option StrMap.t) 
                           (tlist : string list) (tdict : Lexer.typeDict)
                           sinfo =
            typecheck_p @@ (List.fold_left
            (fun acc (t, name) ->
                try let res_opt = StrMap.find name args in
                    (match res_opt with
                    | Some obj -> 
                        acc && (Ok () = typecheck t obj tlist tdict sinfo)
                    | None ->
                        acc)
                with Not_found -> false) true fields)


        (* 'a is the type of the return of the entire computation -
         * 'b is the type of the "evidence" that the computation returns as it proceeds *)
        type ('a, 'b) delay = Done of ('a * 'b)
                            | Comp of 'b * (unit -> ('a, 'b) delay)

        (* lets you chain together different delays, to make them compose their
         * answers *)
        let rec recurse (x : ('a, 'b) delay res) 
                        (f : 'a * 'b -> ('c, 'b) delay res) : ('c, 'b) delay res= 
            ResultMonad.(>>=) x (fun d ->
                (match d with
                | Done (res, new_state) -> f (res, new_state)
                | Comp (s, g) ->
                    let next = g () in
                    match recurse (Ok next) f with
                    | Ok delay -> Ok (Comp (s, fun () -> delay))
                    | Error e -> Error e))
                    (*Ok (Comp (s, fun state -> 
                    let next = g state in
                        recurse (Ok next) f)))) *)
        let mkComp (s : state) (d : ('a, state) delay res) : ('a, state) delay res =
            match d with
            | Ok delay ->
                Ok (Comp (s, fun () -> delay))
            | Error e -> Error e
        
        type direction = Index of Int32.t
                       | Deref
                       | Field of string
                       | VarName of string

        let add_asgn (a : assign) (s : state) = 
            let (line, asgnlist) = s.asgns in
            {s with asgns = (line, a::asgnlist)}
        
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
            | _ ->
                let var = {name = id; ty = t; data = o; scope = s.scope} in
                let added_stack = StrMap.add id var s.stack in
                let new_state = add_asgn (VarAsgn (None, var)) s in
                Ok {new_state with stack = added_stack}

        let get_var_scope (v : var) = v.scope

        let rec descope (s : state) : state =
            let new_s = {s with scope = s.scope - 1} in
            let new_stack = StrMap.filter (fun k elem -> (get_var_scope elem) <= new_s.scope) new_s.stack in 
            {new_s with stack = new_stack}

        let refocus (s : state) (l : line) : state =
            {s with prev = s.asgns::s.prev; asgns = (l, [])} 

        let replace_stack (new_stack : var StrMap.t) (old_state : state) =
            let stack = old_state.stack in
            let added_asgn = add_asgn (Clear (old_state.stack, new_stack)) old_state in
            let new_state = {added_asgn with stack = new_stack} in
            new_state
        
        (* get_directions evaluates the given AST *)
        let rec get_directions (ast : Pratt.ast) (s : state) 
                           (acc : direction list) : (direction list, state) delay res =
            match ast with
            | UnOp (Asterisk, hole) ->
                get_directions hole s (Deref::acc)
            | DotAccess (hole, field) ->
                get_directions hole s ((Field field)::acc)
            | ArrayAccess (hole, expr) ->
                recurse (eval_exp expr s) (fun (obj, new_state) ->
                    match obj with
                    | IntObj i ->
                        get_directions hole new_state ((Index i)::acc)
                    | _ -> Error "Indexed with a non-IntObj.")
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
                        | ArrObj (t, arr) -> 
                            let old_arr_elem = Array.get arr (Int32.to_int i) in 
                            let* (new_arr_elem, new_state) = follow' xs (old_arr_elem) s in
                            let _ = Array.set arr (Int32.to_int i) (Some new_arr_elem) in
                            let asgn_state = add_asgn 
                                (MutArray (arr, Int32.to_int i, 
                                           old_arr_elem, new_arr_elem)) new_state in
                            Ok (ArrObj (t, arr), asgn_state)
                        | _ -> Error "Got an index with a non-Array object.")
                    
                    | (Deref::xs, Some hole_obj) ->
                        (match hole_obj with 
                        | PtrObj (t, ptr_ref) ->
                            let old_ptr_elem = !ptr_ref in 
                            let* (new_ptr_elem, new_state) = follow' xs (old_ptr_elem) s in
                            let _ = ptr_ref := Some new_ptr_elem in
                            let asgn_state = add_asgn 
                                (MutObj (ptr_ref, old_ptr_elem, new_ptr_elem)) new_state in
                            Ok (PtrObj (t, ptr_ref), asgn_state)
                        | _ -> Error "Got a Deref with a non-Ptr object.")
                    
                    | ((Field name)::xs, Some hole_obj) ->
                        (match hole_obj with
                        | StructObj (t, struct_map) ->
                            let old_struct_elem = StrMap.find name struct_map in
                            let* (new_struct_elem, new_state) = follow' xs (old_struct_elem) s in
                            let new_struct_map = StrMap.add name (Some new_struct_elem) struct_map in
                            Ok (StructObj (t, new_struct_map), s)
                        | _ -> Error "Got a Field with a non-Struct object.")
                    | _ -> Error "Should not be possible") in 


                let* (old_obj, t) = 
                    try let {name=name; ty=t; data=o; _} = StrMap.find name s.stack in
                        Ok (o, t)
                    with Not_found -> Error "Old var not found." in
                let old_var = find_var name s in
                let* (new_obj, new_state) = follow' rest old_obj s in
                let new_var = {name=name; ty=t; data= Some new_obj; scope=new_state.scope} in
                let updated_state = {new_state with stack = StrMap.add name
                (new_var) new_state.stack} in
                let updated_state2 = add_asgn (VarAsgn (old_var, new_var)) updated_state in
                Ok updated_state2
            | _ -> failwith "Impossible."
        
        (* assign takes in the AST of the LHS and RHS, and evaluates the LHS
         * (accounting for any side effects that may occur), then RHS, and
         * composing their delays. returns the state in which the assignment has
         * happened. *)
        and assign (ast : Pratt.ast) (ast2 : Pratt.ast) (s : state) : (unit, state) delay res =
            (* get the delay of finding the directions *)
            let dir_delay = get_directions ast s [] in
            recurse dir_delay (fun (directions, new_state) ->
                (* get the delay of computing the rhs, in the state after doing lhs *)
                let rhs_delay = eval_exp ast2 new_state in 
                recurse rhs_delay (fun (rhs_obj, eval_state) ->
                    let* asgn_state = follow directions eval_state (fun _ -> Ok rhs_obj) in
                    Ok (Done ((), asgn_state))))
        


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
                            assign_ast directions op' new_state rhs_ast)
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
                let+ init = ListStateResMonad.find_symbol Semicolon in
                let+ guard = ListStateResMonad.find_symbol Semicolon in
                let+ step = get in
                return (init, guard, step) in
            let* guard_exp = 
                runState guard @@
                let+ v = Pratt.expr_bp 0 in
                return v in
            let new_state = {s with scope = s.scope + 1} in   
            
            let rec run_for (s : state) : (obj option, state) delay res =
                let refocus_s = refocus s guard in
                (*mkComp refocus_s *)
                Ok (Comp (refocus_s, fun () ->
                recurse (eval_exp guard_exp refocus_s) (fun (guard_obj, guarded_state) ->
                match guard_obj with
                | BoolObj b -> 
                    if b then 
                        let up_state = {guarded_state with scope =
                            guarded_state.scope + 1} in 
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

            let refocus_s = refocus new_state init in
            Comp (refocus_s, fun () ->
                let* init_delay = eval_line init refocus_s in
                recurse init_delay (fun ((), init_state) ->
                    run_for init_state))

        and eval_while (line : token list) (ast : statement) (s : state) =
            let* guard_exp =
                runState line @@
                let* v = Pratt.expr_bp 0 in
                return v in
            let up_state = {s with scope = scope + 1} in
            let rec run_while (s : state) : (unit, state) delay res =
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
                let* v = Pratt.expr_bp 0 in 
                return v in
                let refocus_s = refocus s cond in
                Comp (refocus_s, fun () ->
                recurse (eval_exp cond_exp refocus_s) (fun (cond_obj, cond_state) ->
                    match cond_obj with
                    | BoolObj b ->
                        if b then
                            let up_state = {cond_state with scope = scope + 1} in
                            recurse (eval_statement if_ast up_state) (fun (eval_opt, if_state) ->
                                (* TODO: optimize this out later *)
                                match eval_opt with
                                | Some eval_obj -> 
                                    let down_state = descope if_state in
                                    Ok (Done (Some eval_obj, down_state))
                                | _ ->
                                    let down_state = descope if_state in
                                    Ok (Done (None, down_state)))
                        else
                            (match else_ast_opt with
                            | Some else_ast ->
                                let up_state = {cond_state with scope = scope + 1} in
                                recurse (eval_statement else_ast up_state) (fun (eval_opt, else_state) ->
                                    (* this too *)
                                    match eval_opt with
                                    | Some eval_obj -> 
                                        let down_state = descope else_state in
                                        Ok (Done (Some eval_obj, down_state))
                                    | _ -> 
                                        let down_state = descope else_state in
                                        Ok (Done (None, down_state)))
                            | None -> Ok (Done (None, cond_state)))
                    | _ -> Error "Cond returned a non-bool.")) 
                            
        (* when you evaluate a statement, return a continuation to the next
         * thing (and the previous thing), and update the state *)
        (* this is where side effects happen. *)
        and eval_statement (ast : statement)
                               (s: state) : (obj option, state) delay res = 
            match ast with
            | SimpleStmt line ->
                let refocus_s = refocus s line in
                 Comp (refocus_s, fun () -> 
                     recurse (eval_line line refocus_s) (fun ((), line_state) ->
                        Ok (Done (None, line_state))))
            | IfStmt (cond, code, el) -> eval_if cond code el s
            | WhileStmt (cond, code) -> eval_while cond code s
            | ForStmt (line, code) -> eval_for line code s
            | BlockStmt l ->
                let new_state = {s with scope = scope + 1} in
                let folded_delay = 
                    List.fold_left (fun acc stmt ->
                    let* acc_delay = acc in
                    recurse acc_delay (fun (acc_opt, acc_state) ->
                        match acc_opt with
                        | Some ret ->
                            Ok (Done (Some ret, acc_state))
                        | _ ->
                            recurse (eval_statement stmt acc_state) (fun (eval_obj, eval_state) -> 
                            Ok (Done (eval_obj, eval_state))))) (Ok (Done (None, s))) l in
                recurse folded_delay (fun (block_opt, folded_state) ->
                    let down_state = descope folded_state in
                    Ok (Done (block_opt, down_state)))
            | ReturnStmt line ->
                let refocus_s = refocus s (Return::line) in
                Comp (refocus_s, fun () ->
                    let* line_exp = exp_from_line line in 
                    recurse (eval_exp line_exp refocus_s) (fun (eval_obj, eval_state) ->
                    Ok (Done (Some eval_obj, eval_state))))
            | AssertStmt line ->
                let refocus_s = refocus s (Assert::line) in
                Comp (refocus_s, fun s' ->
                    let* line_exp = exp_from_line line in
                    recurse (eval_exp line_exp refocus_s) (fun (eval_obj, eval_state) ->
                    match eval_obj with
                    | BoolObj b ->
                        if b then 
                            Ok (Done (None, eval_state))
                        else
                            Error "Assert failed."
                    | _ -> Error "Non-bool given to Assert."))
            | ErrorStmt line ->
                let refocus_s = refocus s (Error::line) in
                Comp (refocus_s, fun s' ->
                    let* line_exp = exp_from_line line in 
                    recurse (eval_exp line_exp refocus_s) (fun (eval_obj, eval_state) ->
                    match eval_obj with
                    | StrObj s ->
                        Error (Printf.sprintf "Program Error: %s" s)
                    | _ -> Error "Non-string given to Error."))
                

        and eval_function (s : string) (s : state) (arglist: (ty * string * obj) list)
                              (funcmap : func StrMap.t) =
            try (let func_info = StrMap.find s funcmap in
                let old_stack = s.stack in
                let old_scope = cleared_state.scope in
                let cleared_state = replace_stack (StrMap.empty) s in
                let reset_state = {cleared_state with scope = 0} in
                let populated_state = {reset_state with 
                    stack =  
                        List.fold_left (fun acc (t, name, o) ->
                        StrMap.add acc name {name = name; ty = t; data = Some o; scope = 0})
                        stack arglist} in
                recurse (eval_statement func_info.ast populated_state) (fun (eval_opt, eval_state) ->
                    let new_state = replace_stack old_stack eval_state in
                    let reset_state = {new_state with scope = old_scope} in
                    (match eval_opt with
                    | Some eval_obj ->
                        Ok (Done (eval_obj, reset_state))
                    | None ->
                        Ok (Done (VoidObj, reset_state)))))
            with Not_found -> Error "Failed to find function."
                
        and eval_exp (ast : Pratt.ast) (s : state) : (obj, state) delay res = 
            match ast with
            | BinOp (op, lhs, rhs) ->
                (try let (_, f) = List.find (fun (t, _) -> t = op) arith_binops in
                    recurse (eval_exp lhs s) (fun (lhs_res, s') ->
                        recurse (eval_exp rhs s') (fun (rhs_res, s'') ->
                            match (lhs_res, rhs_res) with
                            | (IntObj i1, IntObj i2) -> Ok (Done (IntObj (f i1 i2), s''))
                            | _ -> Error "Did not get IntObj for int BinOps."
                            ))
                with Not_found ->
                    (try let (_, f) = List.find (fun (t, _) -> t = op) bool_binops in
                        recurse (eval_exp lhs s) (fun (lhs_res, s') ->
                            recurse (eval_exp rhs s') (fun (rhs_res, s'') ->
                                match (lhs_res, rhs_res) with
                                | (BoolObj b1, BoolObj b2) -> Ok (Done (BoolObj (f b1 b2), s''))
                                | _ -> Error "Did not get BoolObj for bool BinOps."
                                ))
                    with Not_found -> Error "Invalid op for BinOp."))
            | UnOp (op, arg) ->
                recurse (eval_exp arg s) (fun (res, new_state) ->
                    (match (op, res) with
                    | (Bang, BoolObj b) -> Ok (Done (BoolObj (not b), new_state))
                    | (Tilde, IntObj i) -> Ok (Done (IntObj (Int32.lognot i), new_state))
                    | (Minus, IntObj i) -> Ok (Done (IntObj (Int32.neg i), new_state))
                    | (Asterisk, PtrObj (t, ptr_ref)) ->
                        (match !ptr_ref with
                        | Some ptr_obj ->
                            Ok (Done (ptr_obj, new_state))
                        | None -> Error "Tried to access uninitialized pointer.")
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
                            let* _ = typecheck t eval_obj tlist tdict sinfo in
                            Ok (Done ((t, field, eval_obj)::l, eval_state)))))
                        Ok (Done ([], s)) zipped in
                        recurse before_call (fun (objlist, args_state) ->
                        recurse (eval_function name args_state objlist) (fun (ret_obj, func_state) ->
                        Ok (Done (ret_obj, func_state))))
                with Not_found ->
                    Error "Tried to use nonexistent function.")
            | Name name ->
                (try let var = StrMap.find s.stack name in
                    (match var.data with
                    | Some obj ->
                        Ok (Done (obj, s))
                    | None ->
                        Error "Tried to use value of uninitialized var.")
                with Not_found ->
                    Error "Tried to look up variable that did not exist.")
            | Lit obj -> Ok (Done (obj, s))
            | DotAccess (ast, field) ->
                recurse (eval_exp ast s) (fun (eval_obj, eval_state) ->
                    (match eval_obj with
                    | StructObj (t, s_map) ->
                        (try let res_opt = StrMap.find field s_map in
                            (match res_opt with
                            | Some res_obj -> Ok (Done (res_obj, s))
                            | None -> Error "Referenced uninitialized struct field.")
                        with Not_found ->
                            Error "Field not found.")
                    | _ -> "Tried to access field of non-Struct object."))
            | ArrowAccess (ast, field) ->
                eval_exp (DotAccess (UnOp (Asterisk, ast), field)) s
            | ArrayAccess (ast, index_ast) ->
                recurse (eval_exp ast s) (fun (main_obj, first_state) ->
                recurse (eval_exp index_ast first_state) (fun (index_obj, after_state) ->
                    (match (main_obj, index_obj) with
                    | (ArrObj (t, arr), IntObj i) ->
                        (try let arr_opt = Array.get arr i in
                            (match arr_opt with
                            | Some arr_obj ->
                                Ok (Done (arr_obj, after_state))
                            | None ->
                                Error "Using uninitialized array element.")
                        with Invalid_argument ->
                            Error "Index of int object out of array bounds.")
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
                    
        (*
        let rec eval_expression (ast : ast) : obj m =
            fun alist ->
            runState alist @@ 
            match ast with
            | BinOp (op, lhs, rhs) ->
                let+ obj_l = eval_expression lhs in
                let+ obj_r = eval_expression rhs in
                try let (_, f) = List.find (fun (t, _) -> t = op) arith_binops in
                    (match (obj_l, obj_r) with 
                    | (IntObj i1, IntObj i2) -> return_both @@ IntObj (f i1 i2)
                    | _ -> return_er "Arguments to arithmetic BinOp were not ints.")
                with Not_found ->
                    try let (_, f) = List.find (fun (t, _) -> t = op) bool_binops in 
                    (match (obj_l, obj_r) with
                    | (BoolObj b1, BoolObj b2) -> return_both @@ BoolObj (f b1 b2)
                    | _ -> return_err "Arguments to bool BinOp were not bools.")
                    with Not_found -> return_err "Invalid op for BinOp."
            | UnOp (op, arg) ->
                let* obj = eval_expression arg in
                (match op with
                | Bang ->
                    (match obj with 
                    | BoolObj b -> return_both @@ BoolObj (not b)
                    | _ -> return_err "Logical not of a non-bool.")
                | Tilde ->
                    (match obj with
                    | IntObj i -> return_both @@ IntObj (Int32.lognot i)
                    | _ -> return_err "Bitwise not of a non-int.")
                | Minus -> 
                    (match obj with
                    | IntObj i -> Ok (IntObj (Int32.neg i))
                    | _ -> return_err "Negating a non-int.")
                | _ -> return_err "Invalid op for UnOp.")
            | Call (


        (* returns Ok of the empty object, uninitialized *)
        let init_var (t : ty) (name : string) : var res = 
            (* if you can reduce the type, then the type is valid. *)
            let* _ = Lexer.reduce_type t tdict tlist in
            Ok (name, t, None);

        *)

                (*
        let rec eval_line (line : line) (funcmap : func StrMap.t)  
                          ((prev, next, stack, heap) : state) : state res= 
            match line with 
            | (Type ty)::(Identifier name)::Semicolon::rest ->
                let new_var = (name, ty, 
                Ok ((line, [Change (None, Some  
          *)      
    
        (*let rec eval_program (filename: string) : int =
            let (tokens, tdict, tlist) = Lexer.lex filename in
            let fpool = Parser.gen_function_pool tokens in

                        *)

  end
