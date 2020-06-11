let rec extract_dests seq =
  match seq with
  | Asm.Ans(exp)            ->
      (match exp with
      | IfEq(_,_,e1,e2)
      | IfLE(_,_,e1,e2)
      | IfGE(_,_,e1,e2) -> (extract_dests e1) @ (extract_dests e2)
      | _               -> []
      )
  | Asm.Let((x,_),exp,succ) ->
      x ::
      (match exp with
      | IfEq(_,_,e1,e2)
      | IfLE(_,_,e1,e2)
      | IfGE(_,_,e1,e2) -> (extract_dests e1) @ (extract_dests e2)
      | _               -> []
      ) @
      (extract_dests succ)

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
  | Verilog_comb.Nop        ->p "  wire [31:0] /* Nop*/ %10s = 0;\n" d
  | Verilog_comb.Mov(V(s))  ->p "  wire [31:0] /* Mov*/ %10s = %s;\n" d s
  | Verilog_comb.Mov(C(i))  ->p "  wire [31:0] /* Mov*/ %10s = %d;\n" d i
  | Verilog_comb.Neg(s)     ->p "  wire [31:0] /* Neg*/ %10s = (~%s) + 1;\n" d s
  | Verilog_comb.Add(s,V(t))->p "  wire [31:0] /* Add*/ %10s = $signed(%s) + $signed(%s);\n" d s t
  | Verilog_comb.Add(s,C(i))->p "  wire [31:0] /* Add*/ %10s = $signed(%s) + $signed(%d);\n" d s i
  | Verilog_comb.Sub(s,V(t))->p "  wire [31:0] /* Sub*/ %10s = $signed(%s) - $signed(%s);\n" d s t
  | Verilog_comb.Sub(s,C(i))->p "  wire [31:0] /* Sub*/ %10s = $signed(%s) - $signed(%d);\n" d s i
  | Verilog_comb.IfEq(s,V(t),br1,br2)->
      p "  wire [31:0] /*IfEq*/ %10s =(%s==%s) ? %s : %s;\n" d s t br1 br2
  | Verilog_comb.IfEq(s,C(i),br1,br2)->
      p "  wire [31:0] /*IfEq*/ %10s =(%s==%d) ? %s : %s;\n" d s i br1 br2
  | Verilog_comb.IfLE(s,V(t),br1,br2)->
      p "  wire [31:0] /*IfLE*/ %10s =($signed(%s)<=$signed(%s)) ? %s : %s;\n" d s t br1 br2
  | Verilog_comb.IfLE(s,C(i),br1,br2)->
      p "  wire [31:0] /*IfLE*/ %10s =($signed(%s)<=$signed(%d)) ? %s : %s;\n" d s i br1 br2
  | Verilog_comb.IfGE(s,V(t),br1,br2)->
      p "  wire [31:0] /*IfGE*/ %10s =($signed(%s)>=$signed(%s)) ? %s : %s;\n" d s t br1 br2
  | Verilog_comb.IfGE(s,C(i),br1,br2)->
      p "  wire [31:0] /*IfGE*/ %10s =($signed(%s)>=$signed(%d)) ? %s : %s;\n" d s i br1 br2
  );
  (match succ with
  | None    -> ()
  | Some(s) -> emit_assigns_in_module s
  )

let emit_fsm_in_module args regs fsm =
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
  | []    ->
      begin
        Printf.printf "        default:\n";
        Printf.printf "        begin\n";
        Printf.printf "          // somthing is wrong.\n";
        Printf.printf "          pc <= 0;\n";
        Printf.printf "        end\n";
      end
  | q::rs ->
      begin
        Printf.printf "        %d:\n" q.pc;
        Printf.printf "        begin\n";
        emit_assigns q.assigns;
        (match q.trans with
        | Verilog_seq.Init    ->
            begin
              ignore (
                List.map (fun x -> Printf.printf "          %s <= %s_as_input;\n" x x) args
              );
              Printf.printf "          stack_index <= 1;\n";
              Printf.printf "          pc <= (go) ? 1 : 0; // Init\n"
            end
        | Verilog_seq.Next    -> Printf.printf "          pc <= pc+1; // Next\n"
        | Verilog_seq.Call(g) ->
            begin
              Printf.printf "          %s <= 1;\n" (Verilog_seq.go_common_prefix^"_"^g);
              Printf.printf "          pc <= pc + 1; // Call\n";
            end
        | Verilog_seq.Wait(g) ->
            begin
              Printf.printf "          pc <= (%s) ? pc + 1 : pc; // Wait\n"
              (Verilog_seq.valid_common_prefix^"_"^g);
            end
        | Verilog_seq.Recurse ->
            begin
              ignore (
                List.map (fun x -> Printf.printf "          %s_stack[stack_index] <= %s;\n" x x) (args @ regs)
              );
              Printf.printf "          pc_stack[stack_index] <= pc + 1;\n";
              Printf.printf "          stack_index <= stack_index + 1;\n";
              Printf.printf "          pc <= 1; // Recurse\n";
            end
        | Verilog_seq.Recover ->
            begin
              ignore (
                List.map (fun x -> Printf.printf "          %s <= %s_stack[stack_index];\n" x x) (args @ regs)
              );
              Printf.printf "          pc <= pc + 1; // Recover\n";
            end
        | Verilog_seq.Jump(0) ->
            begin
              Printf.printf "          pc <= pc_stack[stack_index-1]; // Jump(0)\n";
              Printf.printf "          stack_index <= stack_index-1;\n";
            end
        | Verilog_seq.Jump(i) ->
            begin
              Printf.printf "          pc <= %d; // Jump(%d)\n" i i;
            end
        | Verilog_seq.BEq(s,Verilog_seq.V(t),br1,br2) ->
            begin
              Printf.printf "          pc <= (%s==%s) ? %d : %d; // BEq\n" s t br1 br2;
            end
        | Verilog_seq.BEq(s,Verilog_seq.C(i),br1,br2) ->
            begin
              Printf.printf "          pc <= (%s==%d) ? %d : %d; // BEq\n" s i br1 br2;
            end
        | Verilog_seq.BLE(s,Verilog_seq.V(t),br1,br2) ->
            begin
              Printf.printf "          pc <= (%s<=%s) ? %d : %d; // BLE\n" s t br1 br2;
            end
        | Verilog_seq.BLE(s,Verilog_seq.C(i),br1,br2) ->
            begin
              Printf.printf "          pc <= (%s<=%d) ? %d : %d; // BGE\n" s i br1 br2;
            end
        | Verilog_seq.BGE(s,Verilog_seq.V(t),br1,br2) ->
            begin
              Printf.printf "          pc <= (%s>=%s) ? %d : %d; // BGE\n" s t br1 br2;
            end
        | Verilog_seq.BGE(s,Verilog_seq.C(i),br1,br2) ->
            begin
              Printf.printf "          pc <= (%s>=%d) ? %d : %d; // BGE\n" s i br1 br2;
            end
        );
        Printf.printf "        end\n";
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
  let args = f.args @ f.fargs in
  let regs = extract_dests asm_seq
  in
  let Id.L(name) = f.name
  in
  begin
    Printf.printf "module %s\n" name;
    Printf.printf "(\n";
    ignore(List.map (fun x -> Printf.printf "  input wire [31:0] %s_as_input,\n" x) args);
    Printf.printf "  output reg [31:0] %s,\n" Verilog_seq.ret_var;
    Printf.printf "  input wire        go,\n";
    Printf.printf "  output reg        valid,\n";
    Printf.printf "  input wire        clk,\n";
    Printf.printf "  input wire        rstn\n";
    Printf.printf ");\n";
    ignore(List.map (fun x -> Printf.printf "  reg  [31:0] %s;\n"               x) args);
    ignore(List.map (fun x -> Printf.printf "  reg  [31:0] %s_stack [100:0];\n" x) args);
    ignore(List.map (fun x -> Printf.printf "  reg  [31:0] %s;\n"               x) regs);
    ignore(List.map (fun x -> Printf.printf "  reg  [31:0] %s_stack [100:0];\n" x) regs);
    Printf.printf "  reg  [31:0] pc;\n";
    Printf.printf "  reg  [31:0] pc_stack [100:0];\n";
    Printf.printf "  reg  [31:0] stack_index;\n";
    Printf.printf "\n";
    emit_assigns_in_module comb;
    Printf.printf "\n";
    Printf.printf "  assign valid = (stack_index==0);\n";
    Printf.printf "\n";
    Printf.printf "  always @(posedge clk) begin\n";
    Printf.printf "    if (~rstn) begin\n";
    Printf.printf "      stack_index <= 1;\n";
    Printf.printf "      pc          <= 0;\n";
    Printf.printf "      pc_stack[0] <= 0;\n";
    Printf.printf "    end else begin\n";
    emit_fsm_in_module args regs fsm;
    Printf.printf "    end\n";
    Printf.printf "  end\n";
    Printf.printf "\n";
    Printf.printf "endmodule\n";
  end

let rec emit_module_instances instances_and_calls =
  match instances_and_calls with
  | [] -> ()
  | (inst,Asm.CallCls(     g ,args,fargs))::rest
  | (inst,Asm.CallDir(Id.L(g),args,fargs))::rest -> 
      begin
        Printf.printf "  %s %s (\n" g inst;
        ignore (
          List.map (fun x -> Printf.printf "    %s,\n" x) (args @ fargs)
        );
        Printf.printf "    %s,\n" (Verilog_seq.ret_var_common_prefix^"_"^inst);
        Printf.printf "    %s,\n" (Verilog_seq.go_common_prefix^"_"^inst);
        Printf.printf "    %s,\n" (Verilog_seq.valid_common_prefix^"_"^inst);
        Printf.printf "    clk,\n";
        Printf.printf "    rstn\n";
        Printf.printf "  );\n";

        emit_module_instances rest;
      end
  | _ -> failwith "dummy:this cannot be happen."

let emit_main_module (Asm.Prog(data,fundefs,body)) =
  let asm_seq  ,
      asm_comb = Verilog_seq.separate_seq_from_comb body
  in
  let comb = Verilog_comb.make_comb (Id.genid "dummy") asm_comb in
  let fsm  = Verilog_seq.make_fsm {name=Id.L("main");args=[];fargs=[];body=asm_seq;ret=Type.Int}
  in
  let wires =
    (List.map (fun x -> Verilog_seq.valid_common_prefix^"_"^(fst x)) !(Verilog_seq.instances_and_calls))
  in
  let regs =
    (extract_dests asm_seq) @
    (List.map (fun x -> Verilog_seq.go_common_prefix^"_"^(fst x)) !(Verilog_seq.instances_and_calls))
  in
  begin
    Printf.printf "module main\n";
    Printf.printf "(\n";
    Printf.printf "  output reg [31:0] %s,\n" Verilog_seq.ret_var;
    Printf.printf "  input wire        go,\n";
    Printf.printf "  output reg        valid,\n";
    Printf.printf "  input wire        clk,\n";
    Printf.printf "  input wire        rstn\n";
    Printf.printf ");\n";
    Printf.printf "  reg  [31:0] pc;\n";
    Printf.printf "  reg  [31:0] pc_stack [100:0];\n";
    Printf.printf "  reg  [31:0] stack_index;\n";
    Printf.printf "\n";
    ignore(List.map (fun x -> Printf.printf "  reg  [31:0] %s;\n" x) regs);
    Printf.printf "\n";
    ignore(List.map (fun x -> Printf.printf "  wire [31:0] %s;\n" x) wires);
    Printf.printf "\n";
    emit_assigns_in_module comb;
    Printf.printf "\n";
    Printf.printf "  assign valid = (stack_index==0);\n";
    Printf.printf "\n";
    Printf.printf "  always @(posedge clk) begin\n";
    Printf.printf "    if (~rstn) begin\n";
    Printf.printf "      stack_index <= 1;\n";
    Printf.printf "      pc          <= 0;\n";
    Printf.printf "      pc_stack[0] <= 0;\n";
    Printf.printf "    end else begin\n";
    ignore(List.map (fun x -> Printf.printf "      %s <= 0;\n" (Verilog_seq.go_common_prefix^"_"^fst(x))) !(Verilog_seq.instances_and_calls));
    emit_fsm_in_module [] regs fsm;
    Printf.printf "    end\n";
    Printf.printf "  end\n";
    Printf.printf "\n";
    emit_module_instances !(Verilog_seq.instances_and_calls);
    Printf.printf "endmodule\n";
  end
