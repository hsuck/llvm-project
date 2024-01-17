// Author: hsuck

#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Demangle/Demangle.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

// PAC-experiment
#include "llvm/PAC-experiment/OptUtil.h"
#include "llvm/PAC-experiment/PAC.h"

#define DEBUG_TYPE "OptFindCtorsPass"

using namespace llvm;
using namespace llvm::PAC;
using namespace llvm::PAC::OptUtil;

namespace {
struct OptFindCtorsPass : public FunctionPass {
  static char ID;
  OptFindCtorsPass() : FunctionPass(ID) {}
  StringRef getPassName() const override { return DEBUG_TYPE; }
  bool runOnFunction(Function &F) override;
};
} // namespace

char OptFindCtorsPass::ID = 0;

static RegisterPass<OptFindCtorsPass> X("opt-ctors-pass",
                                        "Finding Ctors pass");

Pass *llvm::PAC::createOptFindCtorsPass() { return new OptFindCtorsPass(); }

bool OptFindCtorsPass::runOnFunction(Function &F) {
  return false;
  ItaniumPartialDemangler Demangler;

  if (Demangler.partialDemangle(F.getName().str().c_str())) {
    errs() << getPassName() << ": Failed to demangle name, "
           << F.getName() << '\n';
    return false;
  }

  if (!Demangler.isCtorOrDtor())
    return false;

  size_t size = 1;
  char *buf = static_cast<char *>(std::malloc(size));
  
  outs() << getPassName() << ": " << Demangler.getFunctionBaseName(buf, &size) 
         << " (" << F.getName() << ") is constructor !\n";

  for (auto &BB : F) {
    for (auto &I : BB) {
      if (I.getOpcode() == Instruction::Store) {
        auto SI = dyn_cast<StoreInst>(&I);
        auto src = SI->getValueOperand();
        auto dest = SI->getPointerOperand();
        outs() << "Source: " << *src << '\n';
        outs() << "Destination: " << *dest << '\n';
        outs() << src->getName() << '\n';
        outs() << dest->getName() << '\n';
        outs() << SI->hasMetadata() << '\n';
        outs() << "==============================\n";
      }
    }
  }

  return true;
}
