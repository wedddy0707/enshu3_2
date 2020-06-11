(* Asm.t から verilog を生成するのが目標 *)

type dest = Id.t
type src  = Id.t
type imm  = int

type r_control = (dest * src * src) option
type i_control = (dest * src * imm) option

type control_signal = {
  or_ : r_control;
  ori : i_control;
  add : r_control;
  addi: i_control;
  sub : r_control;
  subi: i_control;
  mul : r_control;
  muli: i_control;
  beq : r_control;
  beqi: i_control;
  bne : r_control;
  bnei: i_control;
  ble : r_control;
  blei: i_control;
  bge : r_control;
  bgei: i_control;
}

type label_or_addr = Label of Id.t | Addr of int

type transition =
  | Halt
  | Next
  | Jump   of label_or_addr
  | Branch of int * int

type state = int * (control_signal * transition)

type fsm = state list (* Finite State Machine は State のリスト *)

let def_sig : control_signal = {
  or_ =None;
  ori =None;
  add =None;
  addi=None;
  sub =None;
  subi=None;
  mul =None;
  muli=None;
  beq =None;
  beqi=None;
  bne =None;
  bnei=None;
  ble =None;
  blei=None;
  bge =None;
  bgei=None
}

let zero         = Id.genid "z" (* ゼロレジスタ *)
let final_output = Id.genid "o" (* 最終的な結果を出力するレジスタ *)


let make_fsm x =
  let rec make_fsm_ pc dest ret_pc = function
    | Asm.Ans exp             ->
        (match exp with
        | Asm.Nop       
        | Asm.Comment _ -> [], pc
        | Asm.Set(i)    -> [(pc,({def_sig with ori=Some(dest,zero,i)},Jump(Addr(ret_pc))))], pc
        | Asm.Mov(s)    -> [(pc,({def_sig with or_=Some(dest,s,zero)},Jump(Addr(ret_pc))))], pc
        | Asm.Neg(s)    -> [(pc,({def_sig with sub=Some(dest,zero,s)},Jump(Addr(ret_pc))))], pc
        | Asm.Add(s,t)
        | Asm.Sub(s,t)  ->
            let signal = match exp with
                         | Asm.Add(_,_) ->
                             (match t with
                             | V(u) -> {def_sig with add =Some(dest,s,u)}
                             | C(i) -> {def_sig with addi=Some(dest,s,i)})
                         | Asm.Sub(_,_) ->
                             (match t with
                             | V(u) -> {def_sig with sub =Some(dest,s,u)}
                             | C(i) -> {def_sig with subi=Some(dest,s,i)})
            in
            [(pc,(signal,Jump(Addr(ret_pc))))], pc
        | Asm.IfEq(s,t,rest1,rest2)
        | Asm.IfLE(s,t,rest1,rest2)
        | Asm.IfGE(s,t,rest1,rest2) ->
            let        pc_to_return = pc + 1 in
            let        pc_if_true   = pc + 2 in
            let rest1_fsm, max_pc1  = make_fsm_ pc_if_true  dest pc_to_return rest1 in
            let        pc_if_false  = max_pc1 + 1 in
            let rest2_fsm, max_pc2  = make_fsm_ pc_if_false dest pc_to_return rest2
            in
            let signal = match exp with
                         | Asm.IfEq(_,_,_,_) ->
                             (match t with
                             | V(u) -> {def_sig with beq =Some(zero,s,u)}
                             | C(i) -> {def_sig with beqi=Some(zero,s,i)})
                         | Asm.IfLE(_,_,_,_) ->
                             (match t with
                             | V(u) -> {def_sig with ble =Some(zero,s,u)}
                             | C(i) -> {def_sig with blei=Some(zero,s,i)})
                         | Asm.IfGE(_,_,_,_) ->
                             (match t with
                             | V(u) -> {def_sig with bge =Some(zero,s,u)}
                             | C(i) -> {def_sig with bgei=Some(zero,s,i)})
            in
            let state_to_branch = (pc,          (signal, Branch(pc+2,max_pc1+1))) in
            let state_to_return = (pc_to_return,(def_sig,Jump  (Addr(ret_pc  ))))
            in
            (state_to_branch::state_to_return::(rest1_fsm @ rest2_fsm), max_pc2)
        )
    | Asm.Let((d,_),exp,rest) ->
        (match exp with
        | Asm.Nop    
        | Asm.Comment _ -> make_fsm_ pc dest ret_pc rest
        | Asm.Set(i) ->
            let rest_fsm,
                max_pc =  make_fsm_ (pc+1) dest ret_pc rest in
            let signal = {def_sig with ori=Some(d,zero,i)}  in
            let state  = (pc,(signal,Next))                 in
            (state::rest_fsm, max_pc)
        | Asm.Mov(s) ->
            let rest_fsm,
                max_pc =  make_fsm_ (pc+1) dest ret_pc rest in
            let signal = {def_sig with ori=Some(d,s,0)}     in
            let state  = (pc,(signal,Next))                 in
            (state::rest_fsm, max_pc)
        | Asm.Neg(s) ->
            let rest_fsm,
                max_pc =  make_fsm_ (pc+1) dest ret_pc rest in
            let signal = {def_sig with sub=Some(d,zero,s)}  in
            let state  = (pc,(signal,Next))                 in
            (state::rest_fsm, max_pc)
        | Asm.Add(s,t)
        | Asm.Sub(s,t) ->
            let rest_fsm,
                max_pc = make_fsm_ (pc+1) dest ret_pc rest
            in
            let signal = match exp with
                         | Asm.Add(_,_) ->
                             (match t with
                             | V(u) -> {def_sig with add =Some(d,s,u)}
                             | C(i) -> {def_sig with addi=Some(d,s,i)})
                         | Asm.Sub(_,_) ->
                             (match t with
                             | V(u) -> {def_sig with sub =Some(d,s,u)}
                             | C(i) -> {def_sig with subi=Some(d,s,i)})
            in
            let state  = (pc,(signal,Next))
            in
            (state::rest_fsm, max_pc)
        | Asm.IfEq(s,t,rest1,rest2)
        | Asm.IfLE(s,t,rest1,rest2)
        | Asm.IfGE(s,t,rest1,rest2) ->
            let        pc_to_return = pc + 1 in
            let        pc_if_true   = pc + 2 in
            let rest1_fsm, max_pc1  = make_fsm_ pc_if_true  d pc_to_return rest1 in
            let        pc_if_false  = max_pc1 + 1                                in
            let rest2_fsm, max_pc2  = make_fsm_ pc_if_false d pc_to_return rest2
            in
            let signal = match exp with
                         | Asm.IfEq(_,_,_,_) ->
                             (match t with
                             | V(u) -> {def_sig with beq =Some(zero,s,u)}
                             | C(i) -> {def_sig with beqi=Some(zero,s,i)})
                         | Asm.IfLE(_,_,_,_) ->
                             (match t with
                             | V(u) -> {def_sig with ble =Some(zero,s,u)}
                             | C(i) -> {def_sig with blei=Some(zero,s,i)})
                         | Asm.IfGE(_,_,_,_) ->
                             (match t with
                             | V(u) -> {def_sig with bge =Some(zero,s,u)}
                             | C(i) -> {def_sig with bgei=Some(zero,s,i)})
            in
            let state_to_branch = (pc,          (signal, Branch(pc+2,max_pc1+1))) in
            let state_to_return = (pc_to_return,(def_sig,Jump  (Addr(max_pc2+1))))
            in
            (state_to_branch::state_to_return::(rest1_fsm @ rest2_fsm), max_pc2)
        )
  in
  let fsm,_ = make_fsm_
              (* initial pc = *) 0
              (* final dest = *) final_output
              (* return  pc = *) 0
              (* Asm.t        *) x
  in
  fsm

let (-->) signal1 signal2 = (* indicates Data Hazard *)
  let dests signal =
    S.union  (match signal.or_   with None->S.empty|Some(d,_,_)->S.singleton d)
    (S.union (match signal.ori   with None->S.empty|Some(d,_,_)->S.singleton d)
    (S.union (match signal.add   with None->S.empty|Some(d,_,_)->S.singleton d)
    (S.union (match signal.addi  with None->S.empty|Some(d,_,_)->S.singleton d)
    (S.union (match signal.sub   with None->S.empty|Some(d,_,_)->S.singleton d)
    (S.union (match signal.subi  with None->S.empty|Some(d,_,_)->S.singleton d)
    (S.union (match signal.mul   with None->S.empty|Some(d,_,_)->S.singleton d)
             (match signal.muli  with None->S.empty|Some(d,_,_)->S.singleton d)))))))
  in
  let srcs signal =
    S.union  (match signal.or_   with None->S.empty|Some(_,s,t)-> S.add t (S.singleton s))
    (S.union (match signal.ori   with None->S.empty|Some(_,s,_)->          S.singleton s )
    (S.union (match signal.add   with None->S.empty|Some(_,s,t)-> S.add t (S.singleton s))
    (S.union (match signal.addi  with None->S.empty|Some(_,s,_)->          S.singleton s )
    (S.union (match signal.sub   with None->S.empty|Some(_,s,t)-> S.add t (S.singleton s))
    (S.union (match signal.subi  with None->S.empty|Some(_,s,_)->          S.singleton s )
    (S.union (match signal.mul   with None->S.empty|Some(_,s,t)-> S.add t (S.singleton s))
             (match signal.muli  with None->S.empty|Some(_,s,_)->          S.singleton s )))))))
  in
  not (S.is_empty (S.inter (dests signal1) (srcs signal2)))

let (->*<-) signal1 signal2 = (* indicates Structural Hazard *)
  ((signal1.or_  <> None)&&(signal2.or_  <> None))||
  ((signal1.ori  <> None)&&(signal2.ori  <> None))||
  ((signal1.add  <> None)&&(signal2.add  <> None))||
  ((signal1.addi <> None)&&(signal2.addi <> None))||
  ((signal1.sub  <> None)&&(signal2.sub  <> None))||
  ((signal1.subi <> None)&&(signal2.subi <> None))||
  ((signal1.mul  <> None)&&(signal2.mul  <> None))||
  ((signal1.muli <> None)&&(signal2.muli <> None))||
  ((signal1.beq  <> None||signal1.beqi <> None||signal1.ble  <> None||signal1.blei <> None||signal1.bge  <> None||signal1.bgei <> None)&&(signal2.beq  <> None||signal2.beqi <> None||signal2.ble  <> None||signal2.blei <> None||signal2.bge  <> None||signal2.bgei <> None))

let signal_merge signal1 signal2 = {def_sig with
  or_ =(if signal1.or_  <> None then signal1.or_  else signal2.or_ );
  ori =(if signal1.ori  <> None then signal1.ori  else signal2.ori );
  add =(if signal1.add  <> None then signal1.add  else signal2.add );
  addi=(if signal1.addi <> None then signal1.addi else signal2.addi);
  sub =(if signal1.sub  <> None then signal1.sub  else signal2.sub );
  subi=(if signal1.subi <> None then signal1.subi else signal2.subi);
  mul =(if signal1.mul  <> None then signal1.mul  else signal2.mul );
  muli=(if signal1.muli <> None then signal1.muli else signal2.muli);
  beq =(if signal1.beq  <> None then signal1.beq  else signal2.beq );
  beqi=(if signal1.beqi <> None then signal1.beqi else signal2.beqi);
  ble =(if signal1.ble  <> None then signal1.ble  else signal2.ble );
  blei=(if signal1.blei <> None then signal1.blei else signal2.blei);
  bge =(if signal1.bge  <> None then signal1.bge  else signal2.bge );
  bgei=(if signal1.bgei <> None then signal1.bgei else signal2.bgei)
}

let rec pc_daruma_drop drop_pc fsm =
  let drop pc = if pc > drop_pc then pc-1 else pc
  in
  match fsm with
  | []               -> []
  | (pc,(s,t))::rest ->
      begin
        let modified_pc = drop pc   in
        let modified_t  = match t with
                          | Jump  (Addr(i)) -> Jump  (Addr(drop i))
                          | Branch(i,j)     -> Branch((drop i),(drop j))
                          | _               -> t
        in
        (modified_pc,(s,modified_t))::(pc_daruma_drop drop_pc rest)
      end

let rec reduce_states fsm =
  let rec reduce_states_ fsm =
    match fsm with
    | []                                -> []
    | (pc1,(signal1,transition1))::rest ->
        begin
          match rest with
          | []                                    -> fsm
          | (pc2,(signal2,transition2))::restrest ->
              begin
                if transition1=Next && not(signal1-->signal2) && not(signal1->*<-signal2)
                then
                  let modified_restrest = pc_daruma_drop pc2 restrest
                  in
                  (pc1, ((signal_merge signal1 signal2), transition2))::(modified_restrest)
                else
                  (pc1, (signal1, transition1))::(reduce_states_ rest)
              end
        end
  in
  reduce_states_ fsm
        
let rec print_fsm fsm =
  let print_control_signal s =
    begin
      (match s.or_  with None->()|Some(d,s,t)->Printf.printf "  $%s <= $%s | $%s\n" d s t);
      (match s.ori  with None->()|Some(d,s,i)->Printf.printf "  $%s <= $%s | %d\n" d s i);
      (match s.add  with None->()|Some(d,s,t)->Printf.printf "  $%s <= $%s + $%s\n" d s t);
      (match s.addi with None->()|Some(d,s,i)->Printf.printf "  $%s <= $%s + %d\n" d s i);
      (match s.sub  with None->()|Some(d,s,t)->Printf.printf "  $%s <= $%s - $%s\n" d s t);
      (match s.subi with None->()|Some(d,s,i)->Printf.printf "  $%s <= $%s - %d\n" d s i);
      (match s.beq  with None->()|Some(_,s,t)->Printf.printf "  $cond <= ($%s==$%s)\n" s t);
      (match s.beqi with None->()|Some(_,s,i)->Printf.printf "  $cond <= ($%s==%d)\n" s i);
    end
  in
  let print_transition t =
    begin
      match t with
      | Halt            -> Printf.printf "  state <= state (Halt)\n"
      | Next            -> Printf.printf "  state <= state + 1 (Next)\n"
      | Jump(Addr (i))  -> Printf.printf "  state <= %d (Jump)\n" i
      | Jump(Label(l))  -> Printf.printf "  state <= %s (Jump)\n" l
      | Branch(i,j)     -> Printf.printf "  state <= (condition) ? %d : %d (Branch)\n" i j
      | _               -> ()
    end
  in
  match fsm with
  | []                             -> ()
  | (pc,(signal,transition))::rest ->
      begin
        Printf.printf "%d:\n" pc;
        print_control_signal signal;
        print_transition transition;
        print_fsm rest
      end
