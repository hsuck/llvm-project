// Author hsuck

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
#include "llvm/CodeGen/RegisterScavenging.h"
#include "llvm/CodeGen/TargetPassConfig.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
// PAC includes
#include "llvm/PAC-experiment/PAC.h"

#define DEBUG_TYPE "AArch64CpiPass"

using namespace llvm;
using namespace llvm::PAC;

namespace {

class AArch64CpiPass : public MachineFunctionPass {
public:
  static char ID;

  AArch64CpiPass() : MachineFunctionPass(ID) {}

  /* StringRef getPassName() const override { return DEBUG_TYPE; } */

  bool doInitialization(Module &M) override;
  bool runOnMachineFunction(MachineFunction &) override;

private:
  const AArch64InstrInfo *TII = nullptr;

  void lowerPAAUTCALL(MachineBasicBlock &MBB, MachineInstr &MI);
  void lowerPAPACIA(MachineBasicBlock &MBB, MachineInstr &MI);

  inline bool handleInsn(MachineBasicBlock &MBB,
                         MachineBasicBlock::instr_iterator &MIi);
  inline void lowerPAAUTIA(MachineBasicBlock &MBB, MachineInstr &MI);
  void lowerPAIntrinsicCommon(MachineBasicBlock &MBB, MachineInstr &MI,
                              const MCInstrDesc &InstrDesc);
  inline bool isPAIntrinsic(unsigned Opcode);
}; // AArch64CpiPass

} // namespace

FunctionPass *llvm::createAArch64CpiPass() { return new AArch64CpiPass(); }

char AArch64CpiPass::ID = 0;

bool AArch64CpiPass::doInitialization(Module &M) { return true; }

bool AArch64CpiPass::runOnMachineFunction(MachineFunction &MF) {
  bool found = false;

  TII = MF.getSubtarget<AArch64Subtarget>().getInstrInfo();

  for (auto &MBB : MF)
    for (auto MIi = MBB.instr_begin(), MIie = MBB.instr_end(); MIi != MIie;
         ++MIi) {
      found = handleInsn(MBB, MIi) || found;
    }

  return found;
}

inline bool AArch64CpiPass::handleInsn(MachineBasicBlock &MBB,
                                       MachineBasicBlock::instr_iterator &MIi) {
  const auto MIOpcode = MIi->getOpcode();

  if (!isPAIntrinsic(MIOpcode))
    return false;

	errs() << *MIi << '\n';

  auto &MI = *MIi--;

  switch (MIOpcode) {
  default:
    llvm_unreachable("Unhandled PA intrinsic!!");
  case AArch64::PA_PACIA:
    lowerPAPACIA(MBB, MI);
    break;
  case AArch64::PA_AUTIA:
    /* lowerPAAUTIA(MBB, MI); */
    break;
  case AArch64::PA_AUTCALL:
    /* lowerPAAUTCALL(MBB, MI); */
    break;
  }

  MI.removeFromParent(); // Remove the PA intrinsic!

  return true;
}

inline bool AArch64CpiPass::isPAIntrinsic(unsigned Opcode) {
  switch (Opcode) {
  case AArch64::PA_PACIA:
  case AArch64::PA_AUTIA:
  case AArch64::PA_AUTCALL:
    return true;
  }

  return false;
}

void AArch64CpiPass::lowerPAPACIA(MachineBasicBlock &MBB, MachineInstr &MI) {
  lowerPAIntrinsicCommon(MBB, MI, TII->get(AArch64::PACIA));
}

void AArch64CpiPass::lowerPAIntrinsicCommon(MachineBasicBlock &MBB,
                                            MachineInstr &MI,
                                            const MCInstrDesc &InstrDesc) {
  auto &mod = MI.getOperand(2);
	auto &src = MI.getOperand(1);
  auto &dst = MI.getOperand(0);
  auto BMI = BuildMI(MBB, MI, MI.getDebugLoc(), InstrDesc);
  BMI.add(dst);
  BMI.add(src);
  BMI.add(mod);
}
