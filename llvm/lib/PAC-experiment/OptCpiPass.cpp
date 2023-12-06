// Author: hsuck

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/AbstractCallSite.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

// PAC-experiment
#include "llvm/PAC-experiment/OptUtil.h"
#include "llvm/PAC-experiment/PAC.h"

using namespace llvm;
using namespace llvm::PAC;
using namespace llvm::PAC::OptUtil;

namespace {
struct OptCpiPass : public FunctionPass {
  static char ID;
  OptCpiPass() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override;

private:
  CallInst *genPACedValue(Function &F, Instruction &I, Value *V);
  bool handleInsn(Function &F, Instruction &I);
  bool handleCallInsn(Function &F, Instruction &I);
  bool handleStoreInsn(Function &F, Instruction &I);
  bool handleSelectInsn(Function &F, Instruction &I);
};
} // namespace

char OptCpiPass::ID = 0;
static RegisterPass<OptCpiPass> X("opt-cpi-pass",
                                  "Code Pointer Integrity pass");

Pass *llvm::PAC::createOptCpiPass() { return new OptCpiPass(); }

bool OptCpiPass::runOnFunction(Function &F) {
  // TODO(hsuck): need to add clang option to determine if this pass runs
  errs() << getPassName() << ": " << F.getName() << '\n';

  if (F.hasFnAttribute("no-pac"))
    return false;

  bool modified = false;
  for (auto &BB : F) {
    for (auto &I : BB) {
      modified |= handleInsn(F, I);
    }
  }
  return modified;
}

bool OptCpiPass::handleInsn(Function &F, Instruction &I) {
  const auto IOpcode = I.getOpcode();
  auto retVal = false;

  switch (IOpcode) {
  case Instruction::Store: {
    errs() << getPassName() << ": " << I << '\n';
    retVal = handleStoreInsn(F, I);
    break;
  }
  case Instruction::Select: {
    errs() << getPassName() << ": " << I << '\n';
    retVal = handleSelectInsn(F, I);
    break;
  }
  case Instruction::Call: {
    errs() << getPassName() << ": " << I << '\n';
    retVal = handleCallInsn(F, I);
    break;
  }
  default:
    break;
  }

  return retVal;
}

bool OptCpiPass::handleStoreInsn(Function &F, Instruction &I) {
  auto SI = dyn_cast<StoreInst>(&I);
  auto paced = genPACedValue(F, I, SI->getValueOperand());
  if (paced == nullptr)
    return false;

  SI->setOperand(0, paced);
  errs() << getPassName() << ": " << I << '\n';

  return true;
}

bool OptCpiPass::handleSelectInsn(Function &F, Instruction &I) {
  auto retVal = false;

  for (unsigned int i = 0; i < I.getNumOperands(); ++i) {
    auto paced = genPACedValue(F, I, I.getOperand(i));
    if (paced != nullptr) {
      retVal = true;
      I.setOperand(i, paced);
    }
  }

  return retVal;
}

bool OptCpiPass::handleCallInsn(Function &F, Instruction &I) {
  auto CI = dyn_cast<CallInst>(&I);

  // handle indirect call
  if (CI->isIndirectCall()) {
    auto calledValue = CI->getCalledOperand();
    auto paced = createPACIntrinsic(F, I, calledValue, Intrinsic::pa_autcall);
    CI->setCalledOperand(paced);
  }

  // sign args which are code pointers
  errs() << "Function arguments:\n";
  for (unsigned int i = 0; i < CI->arg_size(); ++i) {
    auto arg = CI->getArgOperand(i);
    const auto argTy = arg->getType();

    errs() << *arg << '\n';
    errs() << "Type: " << *argTy << '\n';

    auto paced = genPACedValue(F, I, arg);
    if (paced != nullptr)
      CI->setArgOperand(i, paced);
  }
  errs() << "===================\n";

  return true;
}

CallInst *OptCpiPass::genPACedValue(Function &F, Instruction &I, Value *V) {
  // We need to handle two types of function pointer arguments:
  // 1) a direct function
  // 2) a direct function passed via BitCastOperator
  auto VTypeInput = isa<BitCastOperator>(V)
                        ? dyn_cast<BitCastOperator>(V)->getSrcTy()
                        : V->getType();
  auto VInput =
      isa<BitCastOperator>(V) ? dyn_cast<BitCastOperator>(V)->getOperand(0) : V;

  // We can skip if the operand is not function address
  if (!VTypeInput->isPointerTy() || !isa<Function>(VInput) ||
      dyn_cast<Function>(VInput)->isIntrinsic())
    return nullptr;

  // V->getType and VTypeInput should match unless bitcast
  assert((isa<BitCastOperator>(V) || V->getType() == VTypeInput));

  // Create PA intrinsic (pacia)
  errs() << getPassName() << ": "
         << "Create pacia intrinsic here\n"
         << '\n';
  return createPACIntrinsic(F, I, V, Intrinsic::pa_pacia);
}
