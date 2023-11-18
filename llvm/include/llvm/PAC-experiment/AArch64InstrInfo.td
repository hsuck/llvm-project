// Author: hsuck

let isPseudo = 1, hasNoSchedulingInfo = 1 in {
  def PA_PACIA : Pseudo<(outs GPR64:$dst),
                           (ins GPR64:$ptr, GPR64sp:$mod),
                           [(set i64:$dst, (int_pa_pacia GPR64:$ptr, GPR64sp:$mod))],
                           "$dst = $ptr">;

  def PA_PACDA : Pseudo<(outs GPR64:$dst),
                           (ins GPR64:$ptr, GPR64sp:$mod),
                           [(set i64:$dst, (int_pa_pacda GPR64:$ptr, GPR64sp:$mod))],
                           "$dst = $ptr">;

  def PA_XPACD : Pseudo<(outs GPR64:$dst),
                           (ins GPR64:$ptr),
                           [(set i64:$dst, (int_pa_xpacd GPR64:$ptr))],
                           "$dst = $ptr">;

  def PA_AUTIA : Pseudo<(outs GPR64:$dst),
                           (ins GPR64:$ptr, GPR64sp:$mod),
                           [(set i64:$dst, (int_pa_autia GPR64:$ptr, GPR64sp:$mod))],
                           "$dst = $ptr">;

  def PA_AUTDA : Pseudo<(outs GPR64:$dst),
                           (ins GPR64:$ptr, GPR64sp:$mod),
                           [(set i64:$dst, (int_pa_autda GPR64:$ptr, GPR64sp:$mod))],
                           "$dst = $ptr">;

  def PA_AUTCALL : Pseudo<(outs GPR64:$dst),
                           (ins GPR64:$ptr, GPR64sp:$mod),
                           [(set i64:$dst, (int_pa_autcall GPR64:$ptr, GPR64sp:$mod))],
                           "$dst = $ptr">;

  def PA_DATA_PTR: Pseudo<(outs),
                           (ins GPR64:$ptr),
                           [(int_parts_data_pointer_argument GPR64:$ptr)]>;

  let mayStore = 1 in {
    def PA_SPILL: Pseudo <(outs), (ins GPR64z:$ptr, GPR64sp:$Rn, i32imm:$offset), []>;
    def PA_USPILL: Pseudo <(outs), (ins GPR64:$ptr, GPR64sp:$Rn, i32imm:$offset), []>;
  }
  let mayLoad = 1 in {
    def PA_RELOAD: Pseudo <(outs GPR64:$ptr), (ins GPR64sp:$Rn, i32imm:$offset), []>;
    def PA_URELOAD: Pseudo <(outs GPR64:$ptr), (ins GPR64sp:$Rn, i32imm:$offset), []>;
  }
}

let isCall = 1, isTerminator = 1, isReturn = 1, isBarrier = 1, Uses = [SP] in {
  def TCRETURNriAA : Pseudo<(outs), (ins tcGPR64:$dst, i32imm:$FPDiff, GPR64sp:$mod), []>,
                   Sched<[WriteBrReg]>;
  def TCRETURNriAB : Pseudo<(outs), (ins tcGPR64:$dst, i32imm:$FPDiff, GPR64sp:$mod), []>,
                   Sched<[WriteBrReg]>;
}
