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
#include <map>

// PAC-experiment
#include "llvm/PAC-experiment/OptUtil.h"
#include "llvm/PAC-experiment/PAC.h"

#define STATISTICS 0

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
  bool isVoidTyOrVoidFp(Constant *CV);
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

      /* outs() << getPassName() << ": Global name: " << Global->getName() << "\n"; */

      int status = 0;
      char *demangled = NULL;
      if ((demangled = itaniumDemangle(Global->getName().str().c_str(), NULL,
                                       NULL, &status)) != NULL) {
        if (StringRef(demangled).contains("vtable"))
          continue;
      }

      /* outs() << "\t\tValue: " << *CV << "\n"; */
      /* outs() << "\t\tType: " << *CVTy << "\n"; */
      /* outs() << "\t\tGlobal Type: " << *(Global->getType()) << "\n"; */

      if (handle(M, &*Global, CV, CVTy)) {
        if (Global->isConstant())
          Global->setConstant(false);
      }
      /* outs() << "==============================\n"; */
    }
  }

  builder->CreateRetVoid();
  builder = nullptr;
  appendToGlobalCtors(M, funcSignGlobals, 0);

#if STATISTICS == 1
  std::map<const FunctionType *, uint64_t> FuncType;
  std::map<const Type *, uint64_t> IndirectCallType;
  errs() << M.getName() << '\n';
  for (auto &F : M) {
    if (F.getName().equals("__pac_sign_globals") ||
        F.getName().contains("llvm"))
      continue;

    FunctionType *funcTy = F.getFunctionType();
    decltype(FuncType)::iterator id = FuncType.find(funcTy);
    if (id != FuncType.end())
      id->second++;
    else
      FuncType.emplace(funcTy, 1);

    for (auto &BB : F) {
      for (auto &I : BB) {
        if (I.getOpcode() == Instruction::Call) {
          auto CI = dyn_cast<CallInst>(&I);
          if (CI->isIndirectCall()) {
            auto calledValue = CI->getCalledOperand();
            auto calledValueType = calledValue->getType();

            errs() << "Indirect Call Type: " << *calledValueType << '\n';
            if (isa<BitCastOperator>(calledValue)) {
              auto BCO = dyn_cast<BitCastOperator>(calledValue);
              errs() << "Indirect Call Type(Src): " << *(BCO->getSrcTy())
                     << '\n';
              errs() << "Indirect Call Type(Dest): " << *(BCO->getDestTy())
                     << '\n';
            }

            decltype(IndirectCallType)::iterator _id =
                IndirectCallType.find(calledValueType);
            if (_id != IndirectCallType.end())
              _id->second++;
            else
              IndirectCallType.emplace(calledValueType, 1);
          }
        }
      }
    }
  }

  errs() << "Total number of functions: " << FuncType.size() << '\n';
  for (auto funcTy = FuncType.begin(); funcTy != FuncType.end(); ++funcTy) {
    errs() << *(funcTy->first) << ": " << funcTy->second << '\n';
  }

  if (IndirectCallType.size() != 0) {
    errs() << "Total number of indirect call: " << IndirectCallType.size()
           << '\n';
    for (auto indirectCallTy = IndirectCallType.begin();
         indirectCallTy != IndirectCallType.end(); ++indirectCallTy) {
      errs() << *(indirectCallTy->first) << ": " << indirectCallTy->second
             << '\n';
    }
  }
  errs() << "==============================\n";
#endif

  return true;
}

bool OptSignGlobalsPass::needPAC(Constant *CV, PointerType *CVTy) {
  auto VTypeInput = isa<BitCastOperator>(CV)
                        ? dyn_cast<BitCastOperator>(CV)->getSrcTy()
                        : CVTy;
  auto VInput = isa<BitCastOperator>(CV)
                    ? dyn_cast<BitCastOperator>(CV)->getOperand(0)
                    : CV;


  // Is a function pointer, and initializer is not NULL
  if (isa<Function>(VInput) && !dyn_cast<Function>(VInput)->isIntrinsic() &&
      !CV->isNullValue())
    return true;

  return false;
}

bool OptSignGlobalsPass::handle(Module &M, Value *V, Constant *CV, Type *Ty) {
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
  bool retVal = false;

  for (auto i = 0U; i < Ty->getNumElements(); ++i) {
    auto elementPtr = builder->CreateStructGEP(Ty, V, i);
    auto elementCV = CV->getAggregateElement(i);
    auto elementTy = Ty->getElementType(i);
    retVal |= handle(M, elementPtr, elementCV, elementTy);
  }

  return true;
}

bool OptSignGlobalsPass::isVoidTyOrVoidFp(Constant *CV) {
  auto Ty = dyn_cast<BitCastOperator>(CV)->getDestTy()->getPointerElementType();
  // void *
  bool isVoidTy = Ty->isIntegerTy();
  bool isVoidFp = false;

  if (Ty->isFunctionTy()) {
    auto retTy = dyn_cast<FunctionType>(Ty)->getReturnType();
    if (!Ty->getFunctionNumParams() && retTy->isVoidTy())
      isVoidFp = true;
  }

  return isVoidTy | isVoidFp;
}

bool OptSignGlobalsPass::handle(Module &M, Value *V, Constant *CV,
                                PointerType *Ty) {
  /* outs() << getPassName() << ":\t\tValue: " << *CV << "\n"; */
  /* outs() << getPassName() << ":\t\tType: " << *Ty << "\n"; */

  if (!needPAC(CV, Ty))
    return false;

  /* outs() << "\t\tNeed PAC !\n"; */

  auto VTypeInput = (isa<BitCastOperator>(CV) && isVoidTyOrVoidFp(CV))
                  ? dyn_cast<BitCastOperator>(CV)->getSrcTy()
                  : Ty;
  auto VInput = (isa<BitCastOperator>(CV))
              ? dyn_cast<BitCastOperator>(CV)->getOperand(0)
              : CV;

  assert((isa<BitCastOperator>(CV) || Ty == VTypeInput));

  /* outs() << getPassName() << ":\t\tReal value: " << *VInput << "\n"; */
  /* outs() << getPassName() << ":\t\tReal Type: " << *VTypeInput << "\n"; */

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
