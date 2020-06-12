(* 再帰関数を順序回路にするのが目標 *)

type id_or_imm = V of Id.t | C of int

type transition =
  | Init
  | Next
  | Call    of Id.t
  | Wait    of Id.t
  | Recurse
  | Recover
  | Jump    of int
  | BEq     of Id.t * id_or_imm * int * int
  | BLE     of Id.t * id_or_imm * int * int
  | BGE     of Id.t * id_or_imm * int * int

type state = {pc : int; assigns : ((Id.t * Id.t) list); trans : transition}

type fsm = state list

let instances_and_calls = ref []

let      go_common_prefix = "go"
let   valid_common_prefix = "valid"
let ret_var_common_prefix = "ret_var"
let ret_var = Id.genid ret_var_common_prefix

(* Asm.t を順序回路にする部分と組合せ回路にする部分に分ける *)
(* 返り値: (順序回路にする部分, 組合せ回路にする部分)       *)
let rec separate_seq_from_comb body =
  let rec merge body1 body2 =
    match body1 with
    | Asm.Ans(Asm.Nop)     -> body2
    | Asm.Let(xt,exp,succ) -> Asm.Let(xt,exp,(merge succ body2))
    | _                    -> failwith("dummy(merge): This cannot be happen.")
  in
  match body with
  | Asm.Ans(exp)         ->
      begin
        match exp with
        | Asm.Nop
        | Asm.Set(_)
        | Asm.Mov(_)
        | Asm.Neg(_)
        | Asm.Add(_,_)
        | Asm.Sub(_,_) -> let x = Id.genid "hoge" in Asm.Ans(Asm.Mov(x)), Asm.Let((x,Type.Int),exp,Asm.Ans(Asm.(Nop)))
        (* 順序回路にすべき exp *)
        | Asm.CallDir(_,_,_)    -> Asm.Ans(exp), Asm.Ans(Asm.Nop)
        | Asm.CallCls(_,_,_)    -> Asm.Ans(exp), Asm.Ans(Asm.Nop)
        | Asm.IfEq(s,t,br1,br2) ->
            let seq1,comb1 = separate_seq_from_comb br1 in
            let seq2,comb2 = separate_seq_from_comb br2 in
            Asm.Ans(Asm.IfEq(s,t,seq1,seq2)), (merge comb1 comb2)
        | Asm.IfLE(s,t,br1,br2) ->
            let seq1,comb1 = separate_seq_from_comb br1 in
            let seq2,comb2 = separate_seq_from_comb br2 in
            Asm.Ans(Asm.IfLE(s,t,seq1,seq2)), (merge comb1 comb2)
        | Asm.IfGE(s,t,br1,br2) ->
            let seq1,comb1 = separate_seq_from_comb br1 in
            let seq2,comb2 = separate_seq_from_comb br2 in
            Asm.Ans(Asm.IfLE(s,t,seq1,seq2)), (merge comb1 comb2)
      end
  | Asm.Let(xt,exp,succ) ->
      begin
        let seq, comb = separate_seq_from_comb succ
        in
        match exp with
        (* 自然に組合せ回路に変換できる exp *)
        | Asm.Nop
        | Asm.Set(_)
        | Asm.Mov(_)
        | Asm.Neg(_)
        | Asm.Add(_,_)
        | Asm.Sub(_,_)          -> seq, Asm.Let(xt,exp,comb)
        (* 順序回路にすべき exp *)
        | Asm.CallCls(_,_,_)    -> Asm.Let(xt,exp,seq), comb
        | Asm.CallDir(_,_,_)    -> Asm.Let(xt,exp,seq), comb
        | Asm.IfEq(s,t,br1,br2) ->
            let seq1,comb1 = separate_seq_from_comb br1 in
            let seq2,comb2 = separate_seq_from_comb br2 in
            Asm.Let(xt,Asm.IfEq(s,t,seq1,seq2),seq), (merge comb1 (merge comb2 comb))
        | Asm.IfLE(s,t,br1,br2) ->
            let seq1,comb1 = separate_seq_from_comb br1 in
            let seq2,comb2 = separate_seq_from_comb br2 in
            Asm.Let(xt,Asm.IfLE(s,t,seq1,seq2),seq), (merge comb1 (merge comb2 comb))
        | Asm.IfGE(s,t,br1,br2) ->
            let seq1,comb1 = separate_seq_from_comb br1 in
            let seq2,comb2 = separate_seq_from_comb br2 in
            Asm.Let(xt,Asm.IfLE(s,t,seq1,seq2),seq), (merge comb1 (merge comb2 comb))
      end

let rec make_fsm (f:Asm.fundef) =
  (*      
   *      make_fsm_
   *      - FSMを作る関数の本体.
   *      - f : Asm.fundef は自由変数 *)
  let rec make_fsm_ dest curr_pc ret_pc = function
    | Asm.Ans(exp) ->
        (match exp with
        | Asm.Mov(s) ->
            let q = {pc = curr_pc;assigns = [(dest,s)];trans = Jump(ret_pc)}
            in
            ([q],curr_pc)
        | Asm.CallDir(Id.L(g),args,fargs)
        | Asm.CallCls(g,args,fargs) when f.name=Id.L(g) ->
            let assigns1 = List.map2 (fun x y -> (x,y)) (f.args @ f.fargs) (args @ fargs) in
            let assigns2 = [(dest,ret_var)] in
            let assigns3 = []
            in
            let q1 = {pc = curr_pc  ;assigns = assigns1;trans = Recurse     } in
            let q2 = {pc = curr_pc+1;assigns = assigns2;trans = Recover     } in
            let q3 = {pc = curr_pc+2;assigns = assigns3;trans = Jump(ret_pc)}
            in
            ([q1;q2;q3],curr_pc+2)
        | Asm.CallDir(Id.L(g),args,fargs)
        | Asm.CallCls(g,args,fargs) (* otherwise *) ->
            let g_inst = Id.genid (g^"_inst")
            in
            let assigns1 = [] in
            let assigns2 = [(dest,ret_var_common_prefix ^ "_" ^ g_inst)] in
            let assigns3 = []
            in
            let q1 = {pc = curr_pc  ;assigns = assigns1;trans = Call(g_inst)} in
            let q2 = {pc = curr_pc+1;assigns = assigns2;trans = Wait(g_inst)} in
            let q3 = {pc = curr_pc+2;assigns = assigns3;trans = Jump(ret_pc)}
            in
            (instances_and_calls := (f.name,g_inst, exp) :: (!instances_and_calls));
            ([q1;q2;q3],curr_pc+3)
        | Asm.IfEq(_,_,br1,br2)
        | Asm.IfLE(_,_,br1,br2)
        | Asm.IfGE(_,_,br1,br2) ->
            let      pc_to_join  = curr_pc + 1 in
            let      pc_if_true  = curr_pc + 2 in
            let br1_fsm, max_pc1 = make_fsm_ dest pc_if_true  pc_to_join br1 in
            let      pc_if_false = max_pc1 + 1 in
            let br2_fsm, max_pc2 = make_fsm_ dest pc_if_false pc_to_join br2
            in
            let trans1 = match exp with
                         | IfEq(s,Asm.V(t),_,_) -> BEq(s,V(t),pc_if_true,pc_if_false)
                         | IfLE(s,Asm.V(t),_,_) -> BLE(s,V(t),pc_if_true,pc_if_false)
                         | IfGE(s,Asm.V(t),_,_) -> BGE(s,V(t),pc_if_true,pc_if_false)
                         | IfEq(s,Asm.C(i),_,_) -> BEq(s,C(i),pc_if_true,pc_if_false)
                         | IfLE(s,Asm.C(i),_,_) -> BLE(s,C(i),pc_if_true,pc_if_false)
                         | IfGE(s,Asm.C(i),_,_) -> BGE(s,C(i),pc_if_true,pc_if_false) in
            let trans2 = Jump(ret_pc)
            in
            let q1 = {pc = curr_pc   ;assigns = [];trans = trans1} in
            let q2 = {pc = pc_to_join;assigns = [];trans = trans2}
            in
            (q1 :: q2 :: (br1_fsm @ br2_fsm), max_pc2)
        )
    | Asm.Let((x,_),exp,succ) ->
        (match exp with
        | Asm.Set(_) -> failwith "これ?"
        | Asm.Mov(s) ->
            let q = {pc = curr_pc;assigns = [(x,s)];trans = Next}
            in
            ([q],curr_pc)
        | Asm.CallDir(Id.L(g),args,fargs)
        | Asm.CallCls(g,args,fargs) when f.name=Id.L(g) ->
            let assigns1 = List.map2 (fun x y -> (x,y)) (f.args @ f.fargs) (args @ fargs) in
            let assigns2 = [(x,ret_var)]
            in
            let q1 = {pc = curr_pc  ;assigns = assigns1;trans = Recurse} in
            let q2 = {pc = curr_pc+1;assigns = assigns2;trans = Recover}
            in
            let succ_fsm,succ_max_pc = make_fsm_ dest (curr_pc+2) ret_pc succ
            in
            ([q1;q2] @ succ_fsm, succ_max_pc)
        | Asm.CallDir(Id.L(g),args,fargs)
        | Asm.CallCls(g,args,fargs) (* otherwise *) ->
            let g_inst = Id.genid (g^"_inst")
            in
            let assigns1 = [] in
            let assigns2 = [(x,ret_var_common_prefix ^ "_" ^ g_inst)]
            in
            let q1 = {pc = curr_pc  ;assigns = assigns1;trans = Call(g_inst)} in
            let q2 = {pc = curr_pc+1;assigns = assigns2;trans = Wait(g_inst)}
            in
            let succ_fsm,succ_max_pc = make_fsm_ dest (curr_pc+2) ret_pc succ
            in
            (instances_and_calls := (f.name, g_inst, exp) :: (!instances_and_calls));
            ([q1;q2] @ succ_fsm, succ_max_pc)
        | Asm.IfEq(_,_,br1,br2)
        | Asm.IfLE(_,_,br1,br2)
        | Asm.IfGE(_,_,br1,br2) ->
            let      pc_to_join  = curr_pc + 1 in
            let      pc_if_true  = curr_pc + 2 in
            let br1_fsm, max_pc1 = make_fsm_ dest pc_if_true  pc_to_join br1 in
            let      pc_if_false = max_pc1 + 1 in
            let br2_fsm, max_pc2 = make_fsm_ dest pc_if_false pc_to_join br2
            in
            let trans1 = match exp with
                         | IfEq(s,Asm.V(t),_,_) -> BEq(s,V(t),pc_if_true,pc_if_false)
                         | IfLE(s,Asm.V(t),_,_) -> BLE(s,V(t),pc_if_true,pc_if_false)
                         | IfGE(s,Asm.V(t),_,_) -> BGE(s,V(t),pc_if_true,pc_if_false)
                         | IfEq(s,Asm.C(i),_,_) -> BEq(s,C(i),pc_if_true,pc_if_false)
                         | IfLE(s,Asm.C(i),_,_) -> BLE(s,C(i),pc_if_true,pc_if_false)
                         | IfGE(s,Asm.C(i),_,_) -> BGE(s,C(i),pc_if_true,pc_if_false) in
            let trans2 = Jump(max_pc2 + 1)
            in
            let q1 = {pc = curr_pc   ;assigns = [];trans = trans1} in
            let q2 = {pc = pc_to_join;assigns = [];trans = trans2}
            in
            let succ_fsm,succ_max_pc = make_fsm_ dest (max_pc2 + 1) ret_pc succ
            in
            ([q1;q2] @ br1_fsm @ br2_fsm @ succ_fsm, max_pc2)
        )
  in
  let q0     = {pc = 0;assigns = [];trans = Init} in
  let fsm    ,
      max_pc = make_fsm_ ret_var 1 0 f.body
  in
  q0 :: fsm

