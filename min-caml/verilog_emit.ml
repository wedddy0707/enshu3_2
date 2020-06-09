let rec emit_module_io args =
  match args with
  | []    ->
      begin
        Printf.printf "  output reg [31:0] %s,\n" Verilog_seq.ret_var;
        Printf.printf "  input wire        go,\n";
        Printf.printf "  output reg        valid,\n";
        Printf.printf "  input wire        clk,\n";
        Printf.printf "  input wire        rstn\n";
      end
  | x::ys ->
      begin
        Printf.printf "  input wire [31:0] %s_as_input,\n" x;
        emit_module_io ys;
      end

let emit_reg_definitions args seq =
  let rec emit_reg_definitions_args args =
    match args with
    | []    -> ()
    | x::ys ->
        begin
          Printf.printf "  reg [31:0] %s;\n" x;
          Printf.printf "  reg [31:0] %s_stack [100:0];\n" x;
          emit_reg_definitions_args ys;
        end
  in
  let rec emit_reg_definitions_seq (seq:Asm.t) =
    match seq with
    | Asm.Ans(_)            -> ()
    | Asm.Let((x,_),_,succ) ->
        begin
          Printf.printf "  reg [31:0] %s;\n" x;
          emit_reg_definitions_seq succ;
        end
  in
  begin
    Printf.printf "  reg [31:0] stack_index;\n";
    Printf.printf "  reg [31:0] pc;\n";
    Printf.printf "  reg [31:0] pc_stack [100:0];\n";

    emit_reg_definitions_args args;
    emit_reg_definitions_seq  seq ;
  end

(* module 内での assign 文の場合 *)
let rec emit_assigns_in_module comb =
  let p = Printf.printf (* 何度も使うので略記を定義しておく *)
  in
  let d,exp,succ = (* destination, expression, succeeding assigns *)
    match comb with
    | Verilog_comb.Return(d,exp)      -> d,exp,None
    | Verilog_comb.Assign(d,exp,succ) -> d,exp,Some(succ)
  in
  (match exp with
  | Verilog_comb.Nop        ->p "  wire [31:0] %s = 0; /* Nop */\n" d
  | Verilog_comb.Mov(V(s))  ->p "  wire [31:0] %s = %s; /* Mov */\n" d s
  | Verilog_comb.Mov(C(i))  ->p "  wire [31:0] %s = %d; /* Mov */\n" d i
  | Verilog_comb.Neg(s)     ->p "  wire [31:0] %s = (~%s) + 1; /* Neg */\n" d s
  | Verilog_comb.Add(s,V(t))->p "  wire [31:0] %s = $signed(%s) + $signed(%s); /* Add */\n" d s t
  | Verilog_comb.Add(s,C(i))->p "  wire [31:0] %s = $signed(%s) + $signed(%d); /* Add */\n" d s i
  | Verilog_comb.Sub(s,V(t))->p "  wire [31:0] %s = $signed(%s) - $signed(%s); /* Sub */\n" d s t
  | Verilog_comb.Sub(s,C(i))->p "  wire [31:0] %s = $signed(%s) - $signed(%d); /* Sub */\n" d s i
  | Verilog_comb.IfEq(s,V(t),br1,br2)->
      p "  wire [31:0] %s =(%s==%s) ? %s : %s; /* IfEq */\n" d s t br1 br2
  | Verilog_comb.IfEq(s,C(i),br1,br2)->
      p "  wire [31:0] %s =(%s==%d) ? %s : %s; /* IfEq */\n" d s i br1 br2
  | Verilog_comb.IfLE(s,V(t),br1,br2)->
      p "  wire [31:0] %s =($signed(%s)<=$signed(%s)) ? %s : %s; /* IfLE */\n" d s t br1 br2
  | Verilog_comb.IfLE(s,C(i),br1,br2)->
      p "  wire [31:0] %s =($signed(%s)<=$signed(%d)) ? %s : %s; /* IfLE */\n" d s i br1 br2
  | Verilog_comb.IfGE(s,V(t),br1,br2)->
      p "  wire [31:0] %s =($signed(%s)>=$signed(%s)) ? %s : %s; /* IfGE */\n" d s t br1 br2
  | Verilog_comb.IfGE(s,C(i),br1,br2)->
      p "  wire [31:0] %s =($signed(%s)>=$signed(%d)) ? %s : %s; /* IfGE */\n" d s i br1 br2
  );
  (match succ with
  | None    ->
      begin
        p "  assign valid = (stack_index==0);\n"
      end
  | Some(s) -> emit_assigns_in_module s
  )

let emit_fsm_in_module args fsm =
  let rec emit_assigns assigns =
    match assigns with
    | []        -> ()
    | (x,y)::zs ->
        begin
          Printf.printf "          %s <= %s;\n" x y;
          emit_assigns zs;
        end
  in
  let rec emit_case_sentence (fsm:Verilog_seq.fsm) =
  match fsm with
  | []    -> ()
  | q::rs ->
      begin
        Printf.printf "        %d:\n" q.pc;
        emit_assigns q.assigns;
        (match q.trans with
        | Verilog_seq.Init    ->
            begin

              ignore (
                List.map (fun x -> Printf.printf "          %s <= %s_as_input;\n" x x) args
              );
              Printf.printf "          stack_index <= 1;\n";
              Printf.printf "          pc <= (go) ? 1 : 0;\n"
            end
        | Verilog_seq.Next    -> Printf.printf "          pc <= pc+1;\n"
        | Verilog_seq.Recurse ->
            begin
              ignore (
                List.map (fun x -> Printf.printf "          %s_stack[stack_index] <= %s;\n" x x) args
              );
              Printf.printf "          pc_stack[stack_index] <= pc + 1;\n";
              Printf.printf "          stack_index <= stack_index + 1;\n";
              Printf.printf "          pc <= 1;\n";
            end
        | Verilog_seq.Recover ->
            begin
              ignore (
                List.map (fun x -> Printf.printf "          %s <= %s_stack[stack_index];\n" x x) args
              );
              Printf.printf "          pc <= pc + 1;\n";
            end
        | Verilog_seq.Jump(0) ->
            begin
              Printf.printf "          pc <= pc_stack[stack_index-1];\n";
              Printf.printf "          stack_index <= stack_index-1;\n";
            end
        | Verilog_seq.Jump(i) ->
            begin
              Printf.printf "          pc <= %d;\n" i;
            end
        | Verilog_seq.BEq(s,Verilog_seq.V(t),br1,br2) ->
            begin
              Printf.printf "          pc <= (%s==%s) ? %d : %d;\n" s t br1 br2;
            end
        | Verilog_seq.BEq(s,Verilog_seq.C(i),br1,br2) ->
            begin
              Printf.printf "          pc <= (%s==%d) ? %d : %d;\n" s i br1 br2;
            end
        | Verilog_seq.BLE(s,Verilog_seq.V(t),br1,br2) ->
            begin
              Printf.printf "          pc <= (%s<=%s) ? %d : %d;\n" s t br1 br2;
            end
        | Verilog_seq.BLE(s,Verilog_seq.C(i),br1,br2) ->
            begin
              Printf.printf "          pc <= (%s<=%d) ? %d : %d;\n" s i br1 br2;
            end
        | Verilog_seq.BGE(s,Verilog_seq.V(t),br1,br2) ->
            begin
              Printf.printf "          pc <= (%s>=%s) ? %d : %d;\n" s t br1 br2;
            end
        | Verilog_seq.BGE(s,Verilog_seq.C(i),br1,br2) ->
            begin
              Printf.printf "          pc <= (%s>=%d) ? %d : %d;\n" s i br1 br2;
            end
        );
        emit_case_sentence rs
      end
  in
  begin

    Printf.printf "      case(pc)\n";    

    emit_case_sentence fsm;

    Printf.printf "      endcase\n";
  end


let rec emit_function_module (f:Asm.fundef) =
  let asm_seq  ,
      asm_comb = Verilog_seq.separate_seq_from_comb f.body
  in
  let comb = Verilog_comb.make_comb (Id.genid "dummy") asm_comb in
  let fsm  = Verilog_seq.make_fsm {f with body = asm_seq}
  in
  let Id.L(name) = f.name
  in
  begin
    Printf.printf "module %s\n" name;
    Printf.printf "(\n";

    emit_module_io (f.args @ f.fargs);

    Printf.printf ");\n";
    

    emit_reg_definitions (f.args @ f.fargs) asm_seq;

    Printf.printf "\n";
    
    emit_assigns_in_module comb;

    Printf.printf "\n";
    Printf.printf "  always @(posedge clk) begin\n";
    Printf.printf "    if (~rstn) begin\n";
    Printf.printf "      stack_index <= 1;\n";
    Printf.printf "      pc          <= 0;\n";
    Printf.printf "      pc_stack[0] <= 0;\n";

    Printf.printf "    end else begin\n";
    
    emit_fsm_in_module (f.args @ f.fargs) fsm;

    Printf.printf "    end\n";
    Printf.printf "  end\n";
    Printf.printf "\n";
    
    Printf.printf "endmodule\n";
  end

(*
let emit_function_definition fundef : Asm.fundef =
  begin
    Printf.printf "function %s" fundef.name;
    Printf.printf "(\n";

    emit_function_args (fundef.args @ fundef.fargs);
    
    Printf.printf ");\n";
    Printf.printf "begin\n";

    emit_assigns (make_assign_assigns fundef.name fundef.body);

    Printf.printf "end\n";
    Printf.printf "endfunction\n";
  end
*)

(*
let rec emit_assigns_in_function comb =
  let p = Prtinf.printf (* 何度も使うので略記を定義しておく *)
  in
  let d,exp,succ = (* destination, expression, succeeding assigns *)
    match comb with
    | Verilog_comb.Return(d,exp)      -> d,exp,None
    | Verilog_comb.Assign(d,exp,succ) -> d,exp,Some(succ)
  in
  (match exp with
  | Verilog_comb.Nop        ->p "%s = 0; /* Nop */\n" d
  | Verilog_comb.Mov(V(s))  ->p "%s = %s; /* Mov */\n" d s
  | Verilog_comb.Mov(C(i))  ->p "%s = %d; /* Mov */\n" d i
  | Verilog_comb.Neg(s)     ->p "%s = (~%s) + 1; /* Neg */\n" d s
  | Verilog_comb.Add(s,V(t))->p "%s = $signed(%s) + $signed(%s); /* Add */\n" d s t
  | Verilog_comb.Add(s,C(i))->p "%s = $signed(%s) + $signed(%d); /* Add */\n" d s i
  | Verilog_comb.Sub(s,V(t))->p "%s = $signed(%s) - $signed(%s); /* Sub */\n" d s t
  | Verilog_comb.Sub(s,C(i))->p "%s = $signed(%s) - $signed(%d); /* Sub */\n" d s i
  | Verilog_comb.IfEq(s,V(t),br1,br2)->
      p "%s =(%s==%s) ? %s : %s; /* IfEq */\n" d s t br1 br2
  | Verilog_comb.IfEq(s,C(i),br1,br2)->
      p "%s =(%s==%d) ? %s : %s; /* IfEq */\n" d s i br1 br2
  | Verilog_comb.IfLE(s,V(t),br1,br2)->
      p "%s =($signed(%s)<=$signed(%s)) ? %s : %s; /* IfLE */\n" d s t br1 br2
  | Verilog_comb.IfLE(s,C(i),br1,br2)->
      p "%s =($signed(%s)<=$signed(%d)) ? %s : %s; /* IfLE */\n" d s i br1 br2
  | Verilog_comb.IfGE(s,V(t),br1,br2)->
      p "%s =($signed(%s)>=$signed(%s)) ? %s : %s; /* IfGE */\n" d s t br1 br2
  | Verilog_comb.IfGE(s,C(i),br1,br2)->
      p "%s =($signed(%s)>=$signed(%d)) ? %s : %s; /* IfGE */\n" d s i br1 br2
  );
  (match succ with
  | None    -> ()
  | Some(s) -> emit_assigns_in_function s
  )
*)
(*
let rec emit_function_args args =
  match args with
  | []    -> ()
  | x::[] -> Printf.printf "  input [31:0] %s\n" x
  | x::ys ->
      begin
        Printf.printf "  input [31:0] %s,\n" x;
        emit_function_args ys;
      end
*)
