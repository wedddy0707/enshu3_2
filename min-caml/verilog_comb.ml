
type id_or_imm = V of Id.t | C of int

type exp =
  | Nop
  | Mov  of        id_or_imm
  | Or   of Id.t * id_or_imm
  | Neg  of Id.t
  | Add  of Id.t * id_or_imm
  | Sub  of Id.t * id_or_imm
  | IfEq of Id.t * id_or_imm * Id.t * Id.t
  | IfLE of Id.t * id_or_imm * Id.t * Id.t
  | IfGE of Id.t * id_or_imm * Id.t * Id.t

type t =
  | Return of Id.t * exp
  | Assign of Id.t * exp * t


let rec make_assign_sequence ret_var body =
  match body with
  | Asm.Ans(exp) ->
      (match exp with
      (* 組合せ回路に変換できないものが来たら fail *)
      | Asm.SetL   (_)        -> failwith(   "SetL can't be converted into combination circuits.")
      | Asm.Ld     (_,_,_)    -> failwith(     "Ld can't be converted into combination circuits.")
      | Asm.St     (_,_,_)    -> failwith(     "St can't be converted into combination circuits.")
      | Asm.LdDF   (_,_,_)    -> failwith(   "LdDF can't be converted into combination circuits.")
      | Asm.StDF   (_,_,_)    -> failwith(   "StDF can't be converted into combination circuits.")
      | Asm.CallCls(_,_,_)    -> failwith("CallCls can't be converted into combination circuits.")
      | Asm.CallDir(_,_,_)    -> failwith("CallDir can't be converted into combination circuits.")
      | Asm.Save   (_,_)      -> failwith(   "Save can't be converted into combination circuits.")
      | Asm.Restore(_)        -> failwith("Restore can't be converted into combination circuits.")
      (* 意味をなさない命令は Nop に *)
      | Asm.Comment(_)
      | Asm.Nop               -> Return(ret_var,Nop)
      (* 以下のものは組合せ回路に変換できる *)
      | Asm.Set(i)            -> Return(ret_var,Mov(C(i)))
      | Asm.Mov(s)            -> Return(ret_var,Mov(V(s)))
      | Asm.Neg(s)            -> Return(ret_var,Neg(  s ))
      | Asm.Add(s,Asm.C(i))   -> Return(ret_var,Add(s,C(i))
      | Asm.Add(s,Asm.V(t))   -> Return(ret_var,Add(s,V(t))
      | Asm.Sub(s,Asm.C(i))   -> Return(ret_var,Sub(s,C(i))
      | Asm.Sub(s,Asm.V(t))   -> Return(ret_var,Sub(s,V(t))
      | Asm.IfEq(s,t,br1,br2) ->
          begin
            let br1_ret_var = Id.genid "br1" in
            let br2_ret_var = Id.genid "br2" in
            let br1_seq = make_assign_sequence br1_ret_var br1 in
            let br2_seq = make_assign_sequence br2_ret_var br2 in
            Return (
              ret_var,
              IfEq (
                s,
                (match t with Asm.V(v)->V(v)|Asm.C(c)->C(c)),
                br1_ret_var,
                br2_ret_var
              )
            )
          end
      | Asm.IfLE(s,t,br1,br2) ->
          begin
            let br1_ret_var = Id.genid "br1" in
            let br2_ret_var = Id.genid "br2" in
            let br1_seq = make_assign_sequence br1_ret_var br1 in
            let br2_seq = make_assign_sequence br2_ret_var br2 in
            Return (
              ret_var,
              IfLE (
                s,
                (match t with Asm.V(v)->V(v)|Asm.C(c)->C(c)),
                br1_ret_var,
                br2_ret_var
              )
            )
          end
      | Asm.IfGE(s,t,br1,br2) ->
          begin
            let br1_ret_var = Id.genid "br1" in
            let br2_ret_var = Id.genid "br2" in
            let br1_seq = make_assign_sequence br1_ret_var br1 in
            let br2_seq = make_assign_sequence br2_ret_var br2 in
            Return (
              ret_var,
              IfLE (
                s,
                (match t with Asm.V(v)->V(v)|Asm.C(c)->C(c)),
                br1_ret_var,
                br2_ret_var
              )
            )
          end
      )
  | Asm.Let((x,_),exp,succ) -> (* Asm.Ans(exp) とほとんど同じことをする *)
      (match exp with
      (* 組合せ回路に変換できないものが来たら fail *)
      | Asm.SetL   (_)        -> failwith(   "SetL can't be converted into combination circuits.")
      | Asm.Ld     (_,_,_)    -> failwith(     "Ld can't be converted into combination circuits.")
      | Asm.St     (_,_,_)    -> failwith(     "St can't be converted into combination circuits.")
      | Asm.LdDF   (_,_,_)    -> failwith(   "LdDF can't be converted into combination circuits.")
      | Asm.StDF   (_,_,_)    -> failwith(   "StDF can't be converted into combination circuits.")
      | Asm.CallCls(_,_,_)    -> failwith("CallCls can't be converted into combination circuits.")
      | Asm.CallDir(_,_,_)    -> failwith("CallDir can't be converted into combination circuits.")
      | Asm.Save   (_,_)      -> failwith(   "Save can't be converted into combination circuits.")
      | Asm.Restore(_)        -> failwith("Restore can't be converted into combination circuits.")
      (* 意味をなさない命令(assignするものがない命令)が来たら困る *)
      | Asm.Comment(_)
      | Asm.Nop               -> failwith("the destination of \"assign\" is not specified.")
      (* 以下のものは組合せ回路に変換できる *)
      | Asm.Set(i)            -> Assign(x,Mov(C(i)) ,(make_assign_sequence ret_var succ))
      | Asm.Mov(s)            -> Assign(x,Mov(V(s)) ,(make_assign_sequence ret_var succ))
      | Asm.Neg(s)            -> Assign(x,Neg(  s ) ,(make_assign_sequence ret_var succ))
      | Asm.Add(s,Asm.C(i))   -> Assign(x,Add(s,C(i),(make_assign_sequence ret_var succ))
      | Asm.Add(s,Asm.V(t))   -> Assign(x,Add(s,V(t),(make_assign_sequence ret_var succ))
      | Asm.Sub(s,Asm.C(i))   -> Assign(x,Sub(s,C(i),(make_assign_sequence ret_var succ))
      | Asm.Sub(s,Asm.V(t))   -> Assign(x,Sub(s,V(t),(make_assign_sequence ret_var succ))
      | Asm.IfEq(s,t,br1,br2) ->
          begin
            let br1_ret_var = Id.genid "br1" in
            let br2_ret_var = Id.genid "br2" in
            let br1_seq = make_assign_sequence br1_ret_var br1 in
            let br2_seq = make_assign_sequence br2_ret_var br2 in
            Return (
              ret_var,
              IfEq (
                s,
                (match t with Asm.V(v)->V(v)|Asm.C(c)->C(c)),
                br1_ret_var,
                br2_ret_var
              )
            )
          end
      | Asm.IfLE(s,t,br1,br2) ->
          begin
            let br1_ret_var = Id.genid "br1" in
            let br2_ret_var = Id.genid "br2" in
            let br1_seq = make_assign_sequence br1_ret_var br1 in
            let br2_seq = make_assign_sequence br2_ret_var br2 in
            Assign (
              x,
              IfLE (
                s,
                (match t with Asm.V(v)->V(v)|Asm.C(c)->C(c)),
                br1_ret_var,
                br2_ret_var
              ),
              (make_assign_sequence ret_var succ)
            )
          end
      | Asm.IfGE(s,t,br1,br2) ->
          begin
            let br1_ret_var = Id.genid "br1" in
            let br2_ret_var = Id.genid "br2" in
            let br1_seq = make_assign_sequence br1_ret_var br1 in
            let br2_seq = make_assign_sequence br2_ret_var br2 in
            Assign (
              x,
              IfLE (
                s,
                (match t with Asm.V(v)->V(v)|Asm.C(c)->C(c)),
                br1_ret_var,
                br2_ret_var
              ),
              (make_assign_sequence ret_var succ)
            )
          end
      )

let rec emit_function_args args = (* input wire, output wire の宣言 *)
  match args with
  | []    -> ()
  | x::[] -> Printf.printf "  input [31:0] %s\n" x
  | x::ys ->
      begin
        Printf.printf "  input [31:0] %s,\n" x;
        emit_function_args ys;
      end

let rec emit_assign_sequence seq =
  let p = Prtinf.printf (* 何度も使うので略記を定義しておく *)
  in
  let d,exp,succ = (* destination, expression, succeeding sequence *)
    match body with
    | Return(d,exp)      -> d,exp,None
    | Assign(d,exp,succ) -> d,exp,Some(succ)
  in
  (match exp with
  | Nop        ->p "  %s = 0; /* Nop */\n" d
  | Mov(V(s))  ->p "  %s = %s; /* Mov */\n" d s
  | Mov(C(i))  ->p "  %s = %d; /* Mov */\n" d i
  | Neg(s)     ->p "  %s = (~%s) + 1; /* Neg */\n" d s
  | Add(s,V(t))->p "  %s = $signed(%s) + $signed(%s); /* Add */\n" d s t
  | Add(s,C(i))->p "  %s = $signed(%s) + $signed(%d); /* Add */\n" d s i
  | Sub(s,V(t))->p "  %s = $signed(%s) - $signed(%s); /* Sub */\n" d s t
  | Sub(s,C(i))->p "  %s = $signed(%s) - $signed(%d); /* Sub */\n" d s i
  | IfEq(s,V(t),br1,br2)->p "  %s =(%s==%s) ? %s : %s; /* IfEq */\n" d s t br1 br2
  | IfEq(s,C(i),br1,br2)->p "  %s =(%s==%d) ? %s : %s; /* IfEq */\n" d s i br1 br2
  | IfLE(s,V(t),br1,br2)->p "  %s =($signed(%s)<=$signed(%s)) ? %s : %s; /* IfLE */\n" d s t br1 br2
  | IfLE(s,C(i),br1,br2)->p "  %s =($signed(%s)<=$signed(%d)) ? %s : %s; /* IfLE */\n" d s i br1 br2
  | IfGE(s,V(t),br1,br2)->p "  %s =($signed(%s)>=$signed(%s)) ? %s : %s; /* IfGE */\n" d s t br1 br2
  | IfGE(s,C(i),br1,br2)->p "  %s =($signed(%s)>=$signed(%d)) ? %s : %s; /* IfGE */\n" d s i br1 br2
  );
  (match succ with
  | None    -> ()
  | Some(s) -> emit_assign_sequence s
  )

let emit_function_definition fundef : Asm.fundef =
  begin
    Printf.printf "function %s" fundef.name;
    Printf.printf "(\n";

    emit_function_args (fundef.args @ fundef.fargs);
    
    Printf.printf ");\n";
    Printf.printf "begin\n";

    emit_assign_sequence (make_assign_sequence fundef.name fundef.body);

    Printf.printf "end\n";
    Printf.printf "endfunction\n";
  end
