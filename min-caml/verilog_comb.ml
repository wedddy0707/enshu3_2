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

let rec comb_merge comb1 comb2 =
  match comb1 with
  | Return(d,exp)      -> Assign(d,exp,comb2)
  | Assign(d,exp,succ) -> Assign(d,exp,(comb_merge succ comb2))

let rec make_comb ret_var body =
  match body with
  | Asm.Ans(exp) ->
      (match exp with
      (* 組合せ回路に変換できないものが来たら fail *)
      | Asm.SetL   (_)        -> failwith(   "SetL can't be converted into combination circuits.")
      | Asm.Ld     (_,_,_)    -> failwith(     "Ld can't be converted into combination circuits.")
      | Asm.St     (_,_,_,_)  -> failwith(     "St can't be converted into combination circuits.")
      | Asm.LdDF   (_,_,_)    -> failwith(   "LdDF can't be converted into combination circuits.")
      | Asm.StDF   (_,_,_,_)  -> failwith(   "StDF can't be converted into combination circuits.")
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
      | Asm.Add(s,Asm.C(i))   -> Return(ret_var,Add(s,C(i)))
      | Asm.Add(s,Asm.V(t))   -> Return(ret_var,Add(s,V(t)))
      | Asm.Sub(s,Asm.C(i))   -> Return(ret_var,Sub(s,C(i)))
      | Asm.Sub(s,Asm.V(t))   -> Return(ret_var,Sub(s,V(t)))
      | Asm.IfEq(s,t,br1,br2) ->
          begin
            let br1_ret_var = Id.genid "br1" in
            let br2_ret_var = Id.genid "br2" in
            let br1_comb    = make_comb br1_ret_var br1 in
            let br2_comb    = make_comb br2_ret_var br2 in
            comb_merge br1_comb (
              comb_merge br2_comb (
                Return (
                  ret_var,
                  IfEq (
                    s,
                    (match t with Asm.V(v)->V(v)|Asm.C(c)->C(c)),
                    br1_ret_var,
                    br2_ret_var
                  )
                )
              )
            )
          end
      | Asm.IfLE(s,t,br1,br2) ->
          begin
            let br1_ret_var = Id.genid "br1" in
            let br2_ret_var = Id.genid "br2" in
            let br1_comb    = make_comb br1_ret_var br1 in
            let br2_comb    = make_comb br2_ret_var br2 in
            comb_merge br1_comb (
              comb_merge br2_comb (
                Return (
                  ret_var,
                  IfLE (
                    s,
                    (match t with Asm.V(v)->V(v)|Asm.C(c)->C(c)),
                    br1_ret_var,
                    br2_ret_var
                  )
                )
              )
            )
          end
      | Asm.IfGE(s,t,br1,br2) ->
          begin
            let br1_ret_var = Id.genid "br1" in
            let br2_ret_var = Id.genid "br2" in
            let br1_comb    = make_comb br1_ret_var br1 in
            let br2_comb    = make_comb br2_ret_var br2 in
            comb_merge br1_comb (
              comb_merge br2_comb (
                Return (
                  ret_var,
                  IfGE (
                    s,
                    (match t with Asm.V(v)->V(v)|Asm.C(c)->C(c)),
                    br1_ret_var,
                    br2_ret_var
                  )
                )
              )
            )
          end
      | _ -> failwith "I hope this cannot be happen"
      )
  | Asm.Let((x,_),exp,succ) -> (* Asm.Ans(exp) とほとんど同じことをする *)
      (match exp with
      (* 組合せ回路に変換できないものが来たら fail *)
      | Asm.SetL   (_)        -> failwith(   "SetL can't be converted into combination circuits.")
      | Asm.Ld     (_,_,_)    -> failwith(     "Ld can't be converted into combination circuits.")
      | Asm.St     (_,_,_,_)  -> failwith(     "St can't be converted into combination circuits.")
      | Asm.LdDF   (_,_,_)    -> failwith(   "LdDF can't be converted into combination circuits.")
      | Asm.StDF   (_,_,_,_)  -> failwith(   "StDF can't be converted into combination circuits.")
      | Asm.CallCls(_,_,_)    -> failwith("CallCls can't be converted into combination circuits.")
      | Asm.CallDir(_,_,_)    -> failwith("CallDir can't be converted into combination circuits.")
      | Asm.Save   (_,_)      -> failwith(   "Save can't be converted into combination circuits.")
      | Asm.Restore(_)        -> failwith("Restore can't be converted into combination circuits.")
      (* 意味をなさない命令(assignするものがない命令)が来たら困る *)
      | Asm.Comment(_)
      | Asm.Nop               -> failwith("the destination of \"assign\" is not specified.")
      (* 以下のものは組合せ回路に変換できる *)
      | Asm.Set(i)            -> Assign(x,Mov(C(i))  ,(make_comb ret_var succ))
      | Asm.Mov(s)            -> Assign(x,Mov(V(s))  ,(make_comb ret_var succ))
      | Asm.Neg(s)            -> Assign(x,Neg(  s )  ,(make_comb ret_var succ))
      | Asm.Add(s,Asm.C(i))   -> Assign(x,Add(s,C(i)),(make_comb ret_var succ))
      | Asm.Add(s,Asm.V(t))   -> Assign(x,Add(s,V(t)),(make_comb ret_var succ))
      | Asm.Sub(s,Asm.C(i))   -> Assign(x,Sub(s,C(i)),(make_comb ret_var succ))
      | Asm.Sub(s,Asm.V(t))   -> Assign(x,Sub(s,V(t)),(make_comb ret_var succ))
      | Asm.IfEq(s,t,br1,br2) ->
          begin
            let br1_ret_var = Id.genid "br1" in
            let br2_ret_var = Id.genid "br2" in
            let br1_comb    = make_comb br1_ret_var br1 in
            let br2_comb    = make_comb br2_ret_var br2 in
            comb_merge br1_comb (
              comb_merge br2_comb (
                Assign (
                  x,
                  IfEq (
                    s,
                    (match t with Asm.V(v)->V(v)|Asm.C(c)->C(c)),
                    br1_ret_var,
                    br2_ret_var
                  ),
                  (make_comb ret_var succ)
                )
              )
            )
          end
      | Asm.IfLE(s,t,br1,br2) ->
          begin
            let br1_ret_var = Id.genid "br1" in
            let br2_ret_var = Id.genid "br2" in
            let br1_comb    = make_comb br1_ret_var br1 in
            let br2_comb    = make_comb br2_ret_var br2 in
            comb_merge br1_comb (
              comb_merge br2_comb (
                Assign (
                  x,
                  IfLE (
                    s,
                    (match t with Asm.V(v)->V(v)|Asm.C(c)->C(c)),
                    br1_ret_var,
                    br2_ret_var
                  ),
                  (make_comb ret_var succ)
                )
              )
            )
          end
      | Asm.IfGE(s,t,br1,br2) ->
          begin
            let br1_ret_var = Id.genid "br1" in
            let br2_ret_var = Id.genid "br2" in
            let br1_comb    = make_comb br1_ret_var br1 in
            let br2_comb    = make_comb br2_ret_var br2 in
            comb_merge br1_comb (
              comb_merge br2_comb (
                Assign (
                  x,
                  IfGE (
                    s,
                    (match t with Asm.V(v)->V(v)|Asm.C(c)->C(c)),
                    br1_ret_var,
                    br2_ret_var
                  ),
                  (make_comb ret_var succ)
                )
              )
            )
          end
      | _ -> failwith "I hope this cannot be happen"
      )


