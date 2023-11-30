// Author: hsuck

#include <iostream>
// LLVM includes
#include "AArch64.h"
#include "AArch64RegisterInfo.h"
#include "AArch64Subtarget.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/TargetPassConfig.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
// PAC includes
#include "llvm/PAC-experiment/PAC.h"

#define DEBUG_TYPE "AArch64InstSelPass"

using namespace llvm;
using namespace llvm::PAC;

namespace {
class AArch64InstSelPass : public MachineFunctionPass {
public:
  static char ID;
  AArch64InstSelPass() : MachineFunctionPass(ID) {}

  virtual bool doInitialization(Module &M) override;
  bool runOnMachineFunction(MachineFunction &) override;

private:
  const AArch64Subtarget *STI = nullptr;
  const AArch64InstrInfo *TII = nullptr;
  inline bool handleInsn(MachineFunction &MF, MachineBasicBlock &MBB,
                         MachineBasicBlock::instr_iterator &MIi);
  inline MachineInstr *findIndirectCallMI(MachineInstr *MI);
  void triggerCompilationErrorOrphanAUTCALL(MachineBasicBlock &MBB);
  inline bool isIndirectCall(const MachineInstr &MI) const;
  inline const MCInstrDesc &getIndirectAutCall(MachineInstr *MI_indcall);
  inline void replaceBranchByAutBranch(MachineBasicBlock &MBB,
                                       MachineInstr *MI_indcall,
                                       MachineInstr &MI);
  inline void insertCOPYInsn(MachineBasicBlock &MBB, MachineInstr *MI_indcall,
                             MachineInstr &MI);
};
} // namespace

FunctionPass *llvm::createAArch64InstSelPass() {
  return new AArch64InstSelPass();
}

char AArch64InstSelPass::ID = 0;

bool AArch64InstSelPass::doInitialization(Module &M) { return true; }

bool AArch64InstSelPass::runOnMachineFunction(MachineFunction &MF) {
  bool found = false;

  STI = &MF.getSubtarget<AArch64Subtarget>();
  TII = STI->getInstrInfo();

  for (auto &MBB : MF)
    for (auto MIi = MBB.instr_begin(), MIie = MBB.instr_end(); MIi != MIie;
         ++MIi)
      found = handleInsn(MF, MBB, MIi) || found;

  return found;
}

inline bool
AArch64InstSelPass::handleInsn(MachineFunction &MF, MachineBasicBlock &MBB,
                               MachineBasicBlock::instr_iterator &MIi) {
  const auto MIOpcode = MIi->getOpcode();

  if (MIOpcode != AArch64::PA_AUTCALL)
    return false;

  errs() << getPassName() << ": " << *MIi << '\n';

  MachineInstr *MI_indcall = findIndirectCallMI(MIi->getNextNode());
	errs() << getPassName() << ": " << *MI_indcall << '\n';
  if (MI_indcall == nullptr)
    triggerCompilationErrorOrphanAUTCALL(MBB);

  auto &MI = *MIi--;
  replaceBranchByAutBranch(MBB, MI_indcall, MI);

  return true;
}

inline const MCInstrDesc &
AArch64InstSelPass::getIndirectAutCall(MachineInstr *MI_indcall) {

  if (MI_indcall->getOpcode() == AArch64::BLR)
    errs() << getPassName() << ": "
           << "Find BLR\n";
  return TII->get(AArch64::BLRAA);

  // This is a tail call return, and we need to use BRAA
  // (tail-call: ~optimizatoin where a tail-cal is converted to a direct call so
  // that the tail-called function can return immediately to the current callee,
  // without going through the currently active function.)

  errs() << getPassName() << ": "
         << "Find BR\n";
  return TII->get(AArch64::TCRETURNriAA);
}

inline MachineInstr *AArch64InstSelPass::findIndirectCallMI(MachineInstr *MI) {
  while (MI != nullptr && !isIndirectCall(*MI))
    MI = MI->getNextNode();

  return MI;
}

inline bool AArch64InstSelPass::isIndirectCall(const MachineInstr &MI) const {
  switch (MI.getOpcode()) {
  case AArch64::BLR:        // Normal indirect call
  case AArch64::TCRETURNri: // Indirect tail call, br
    return true;
  }
  return false;
}

void AArch64InstSelPass::triggerCompilationErrorOrphanAUTCALL(
    MachineBasicBlock &MBB) {
  LLVM_DEBUG(MBB.dump());
  llvm_unreachable("failed to find BLR for AUTCALL");
}

inline void AArch64InstSelPass::replaceBranchByAutBranch(
    MachineBasicBlock &MBB, MachineInstr *MI_indcall, MachineInstr &MI) {
  auto mod = MI.getOperand(2);

  insertCOPYInsn(MBB, MI_indcall, MI);

  auto BMI = BuildMI(MBB, *MI_indcall, MI_indcall->getDebugLoc(),
                     getIndirectAutCall(MI_indcall));

  BMI.addUse(MI_indcall->getOperand(0).getReg());

	// Pseudo<(outs), (ins tcGPR64:$dst, i32imm:$FPDiff), []>
  if (MI_indcall->getOpcode() == AArch64::TCRETURNri)
    // Copy FPDiff from original tail call pseudo instruction
    BMI.add(MI_indcall->getOperand(1));

  BMI.add(mod);
	// Copy arguments
  BMI.copyImplicitOps(*MI_indcall);

  // remove original call pseudo instruction
  MI_indcall->removeFromParent();
  // remove autcall intrinsic
  MI.removeFromParent();
}

inline void AArch64InstSelPass::insertCOPYInsn(MachineBasicBlock &MBB,
                                               MachineInstr *MI_indcall,
                                               MachineInstr &MI) {
  auto dst = MI.getOperand(0);
  auto src = MI.getOperand(1);

  auto COPYMI = BuildMI(MBB, *MI_indcall, MI_indcall->getDebugLoc(),
                        TII->get(AArch64::COPY));
  COPYMI.add(dst);
  COPYMI.add(src);
}
