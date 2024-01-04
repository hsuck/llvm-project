// Author: hsuck

#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringRef.h"
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

using namespace llvm;
using namespace llvm::PAC;
using namespace llvm::PAC::OptUtil;

namespace {
struct OptSignGlobalsPass : public ModulePass {
  static char ID;
  OptSignGlobalsPass() : ModulePass(ID) {}

  IRBuilder<> *builder;

  bool runOnModule(Module &M) override;
  bool needPAC(Constant *CV, PointerType *CVTy);
  bool handle(Module &M, Value *V, Constant *CV, Type *Ty);
  bool handle(Module &M, Value *V, Constant *CV, PointerType *Ty);
  bool handle(Module &M, Value *V, Constant *CV, ArrayType *Ty);
  bool handle(Module &M, Value *V, Constant *CV, StructType *Ty);
};
} // namespace

char OptSignGlobalsPass::ID = 0;
static RegisterPass<OptSignGlobalsPass> X("opt-globals-pass",
                                          "Signing Globals pass");

Pass *llvm::PAC::createOptSignGlobalsPass() { return new OptSignGlobalsPass(); }

bool OptSignGlobalsPass::runOnModule(Module &M) {
  auto &C = M.getContext();
  auto voidTy = Type::getVoidTy(C);
  FunctionType *prototype = FunctionType::get(voidTy, false);
  Function *funcSignGlobals = Function::Create(
      prototype, Function::PrivateLinkage, "__pac_sign_globals", &M);
  funcSignGlobals->addFnAttr("no-pac", "true");
  funcSignGlobals->addFnAttr("noinline", "true");

  auto BB = BasicBlock::Create(M.getContext(), "entry", funcSignGlobals);
  IRBuilder<> localBuilder(BB);
  builder = &localBuilder;

  for (auto Global = M.global_begin(); Global != M.global_end(); ++Global) {
    if (Global->hasInitializer()) {
      const auto CV = Global->getInitializer();
      Type *CVTy = CV->getType();

      if (Global->getName().equals("llvm.global_ctors"))
        continue;

      // TODO(hsuck): sign this global variable.
      if (handle(M, &*Global, CV, CVTy)) {
        outs() << getPassName() << ":\tGlobal name: " << Global->getName() << "\n";
        /* outs() << "Value: " << *CV << "\n"; */
        /* outs() << "Type: " << *CVTy << "\n"; */
        outs() << getPassName() << ":\tGlobal Type: " << *(Global->getType()) << "\n";
        if (Global->isConstant())
          Global->setConstant(false);
        /* outs() << "===============\n"; */
      }
    }
  }

  builder->CreateRetVoid();
  builder = nullptr;
  appendToGlobalCtors(M, funcSignGlobals, 0);

  return true;
}

bool OptSignGlobalsPass::needPAC(Constant *CV, PointerType *CVTy) {
  /* outs() << __FUNCTION__ << '\n'; */
  auto VTypeInput = isa<BitCastOperator>(CV)
                        ? dyn_cast<BitCastOperator>(CV)->getSrcTy()
                        : CVTy;
  auto VInput = isa<BitCastOperator>(CV)
                    ? dyn_cast<BitCastOperator>(CV)->getOperand(0)
                    : CV;

  /* outs() << "Value: " << *VInput << "\n"; */
  /* outs() << "Type: " << *VTypeInput << "\n"; */

  // Is a function pointer, and initializer is not NULL
  if (isa<Function>(VInput) && !dyn_cast<Function>(VInput)->isIntrinsic() &&
      !CV->isNullValue())
    return true;

  return false;
}

bool OptSignGlobalsPass::handle(Module &M, Value *V, Constant *CV, Type *Ty) {
  /* outs() << __FUNCTION__ << '\n'; */
  if (Ty->isArrayTy())
    return handle(M, V, CV, dyn_cast<ArrayType>(Ty));
  if (Ty->isStructTy())
    return handle(M, V, CV, dyn_cast<StructType>(Ty));
  if (Ty->isPointerTy())
    return handle(M, V, CV, dyn_cast<PointerType>(Ty));

  return false;
}
bool OptSignGlobalsPass::handle(Module &M, Value *V, Constant *CV,
                                ArrayType *Ty) {
  /* outs() << __LINE__ << ": " << __FUNCTION__ << '\n'; */

  bool retVal = false;
  auto &C = M.getContext();
  uint64_t baseAddr = 0;

  if (isa<GetElementPtrInst>(V))
    baseAddr = dyn_cast<ConstantInt>(dyn_cast<User>(V)->getOperand(1))
                   ->getLimitedValue();

  for (auto i = 0U; i < Ty->getNumElements(); ++i) {
    auto elementPtr = builder->CreateGEP(
        Ty, V,
        {
            ConstantInt::get(Type::getInt64Ty(C), 0),
            ConstantInt::get(Type::getInt64Ty(C), baseAddr + i),
            /* ConstantInt::get(Type::getInt64Ty(C), i), */
        });
    auto elementCV = CV->getAggregateElement(baseAddr + i);
    /* auto elementCV = CV->getAggregateElement(i); */
    auto elementTy = Ty->getElementType();
    retVal |= handle(M, elementPtr, elementCV, elementTy);
  }

  return retVal;
}
bool OptSignGlobalsPass::handle(Module &M, Value *V, Constant *CV,
                                StructType *Ty) {
  /* outs() << __LINE__ << ": " << __FUNCTION__ << '\n'; */

  bool retVal = false;

  for (auto i = 0U; i < Ty->getNumElements(); ++i) {
    auto elementPtr = builder->CreateStructGEP(Ty, V, i);
    /* outs() << "GEP: " << *elementPtr << '\n'; */
    auto elementCV = CV->getAggregateElement(i);
    auto elementTy = Ty->getElementType(i);
    retVal |= handle(M, elementPtr, elementCV, elementTy);
  }

  return true;
}
bool OptSignGlobalsPass::handle(Module &M, Value *V, Constant *CV,
                                PointerType *Ty) {
  /* outs() << __LINE__ << ": " << __FUNCTION__ << '\n'; */
  outs() << getPassName() << ":\tValue: " << *CV << "\n";
  outs() << getPassName() << ":\tType: " << *Ty << "\n";

  if (!needPAC(CV, Ty))
    return false;

  auto VTypeInput = (isa<BitCastOperator>(CV) &&
                    dyn_cast<BitCastOperator>(CV)->getDestTy()->getPointerElementType()->isIntegerTy())
                  ? dyn_cast<BitCastOperator>(CV)->getSrcTy()
                  : Ty;
  auto VInput = (isa<BitCastOperator>(CV))
              ? dyn_cast<BitCastOperator>(CV)->getOperand(0)
              : CV;

  assert((isa<BitCastOperator>(CV) || Ty == VTypeInput));

  outs() << getPassName() << ":\tReal value: " << *VTypeInput << "\n";
  outs() << getPassName() << ":\tReal Type: " << *VInput << "\n";

  auto casted = isa<BitCastOperator>(CV)
                    ? builder->CreateBitCast(V, VTypeInput->getPointerTo())
                    : V;

  LoadInst *loaded = nullptr;
  if (Ty->isOpaque())
    loaded = builder->CreateLoad(V->getType(), V);
  else
    loaded = builder->CreateLoad(VTypeInput, casted);

  auto paced = createPACIntrinsic(builder, M, loaded, loaded->getType(),
                                  Intrinsic::pa_pacia);
  builder->CreateStore(paced, casted);

  return true;
}
