// Author: hsuck

#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Demangle/Demangle.h"
#include "llvm/IR/AbstractCallSite.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

// PAC-experiment
#include "llvm/PAC-experiment/OptUtil.h"
#include "llvm/PAC-experiment/PAC.h"

#define DEMANGLE_NAME 0
#define CHECK_PAC_BEFORE_AUT 0

#define DEBUG 1

#if DEBUG == 1
#define DEBUG(X)                                                               \
  do {                                                                         \
    X;                                                                         \
  } while (false)
#else
#define DEBUG(X) ((void)0)
#endif

using namespace llvm;
using namespace llvm::PAC;
using namespace llvm::PAC::OptUtil;

namespace llvm {
class TargetLibraryInfo;

struct OptCpiPass : public FunctionPass {
  static char ID;
  OptCpiPass() : FunctionPass(ID) {
    initializeOptCpiPassPass(*PassRegistry::getPassRegistry());
  }
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  bool runOnFunction(Function &F) override;

private:
  std::string skippedFunctions[5] = {"api_", "atexit", "ios_base",
                                     "_ZNSolsEPFRSoS_E", "__cxa_throw"};

  CallInst *genPACedValue(Function &F, Instruction &I, Value *V,
                          Intrinsic::ID intrinsicID);
  bool regenPACedValue(Function &F, Instruction &I, Value *V,
                       Intrinsic::ID intrinsicID);
  bool handleInsn(Function &F, Instruction &I, const TargetLibraryInfo *TLI);
  bool handleCallInsn(Function &F, Instruction &I,
                      const TargetLibraryInfo *TLI);
  bool handleStoreInsn(Function &F, Instruction &I);
  bool handleSelectInsn(Function &F, Instruction &I);
  bool handleInvokeInsn(Function &F, Instruction &I);
  bool isSkippedFuncs(const StringRef &funcName);
};
} // namespace llvm

INITIALIZE_PASS_BEGIN(OptCpiPass, "cpi", "Code Pointer Integrity", false, true)
INITIALIZE_PASS_DEPENDENCY(TargetLibraryInfoWrapperPass)
INITIALIZE_PASS_END(OptCpiPass, "cpi", "Code Pointer Integrity", false, true)

char OptCpiPass::ID = 0;
/* static RegisterPass<OptCpiPass> X("opt-cpi-pass", */
/*                                   "Code Pointer Integrity pass"); */

Pass *llvm::PAC::createOptCpiPass() { return new OptCpiPass(); }

void OptCpiPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequiredTransitive<TargetLibraryInfoWrapperPass>();
  AU.setPreservesAll();
}

bool OptCpiPass::runOnFunction(Function &F) {
  if (F.hasFnAttribute("no-pac") || F.getName().contains("api_"))
    return false;

  DEBUG(outs() << getPassName() << ": " << F.getName() << '\n');

#if DEMANGLE_NAME == 1
  size_t size = 1;
  char *buf = static_cast<char *>(std::malloc(size));
  ItaniumPartialDemangler Demangler;

  if (Demangler.partialDemangle(F.getName().str().c_str())) {
    errs() << getPassName() << ": Failed to demangle name, " << F.getName()
           << '\n';
    goto out;
  }

  if (!Demangler.isCtorOrDtor())
    goto out;

  outs() << getPassName() << ": " << Demangler.getFunctionBaseName(buf, &size)
         << " (" << F.getName() << ") is constructor !\n";
#endif

out:
  const TargetLibraryInfo &TLI =
      getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F);
  bool modified = false;

  for (auto &BB : F) {
    for (auto &I : BB) {
      /* if (F.getName().contains("__cxx_global_var_init")) */
      DEBUG(outs() << getPassName() << ": " << I << '\n');
      modified |= handleInsn(F, I, &TLI);
    }
  }
  return modified;
}

bool OptCpiPass::handleInsn(Function &F, Instruction &I,
                            const TargetLibraryInfo *TLI) {
  const auto IOpcode = I.getOpcode();
  auto retVal = false;

  switch (IOpcode) {
  case Instruction::Store: {
    /* DEBUG(outs() << getPassName() << ": " << I << '\n'); */
    retVal = handleStoreInsn(F, I);
    break;
  }
  case Instruction::Select: {
    /* DEBUG(outs() << getPassName() << ": " << I << '\n'); */
    retVal = handleSelectInsn(F, I);
    break;
  }
  case Instruction::Call: {
    /* DEBUG(outs() << getPassName() << ": " << I << '\n'); */
    retVal = handleCallInsn(F, I, TLI);
    break;
  }
  case Instruction::Invoke: {
    /* DEBUG(outs() << getPassName() << ": " << I << '\n'); */
    retVal = handleInvokeInsn(F, I);
    break;
  }
  default:
    break;
  }

  return retVal;
}

bool OptCpiPass::handleStoreInsn(Function &F, Instruction &I) {

  auto SI = dyn_cast<StoreInst>(&I);

  CallInst *paced =
      genPACedValue(F, I, SI->getValueOperand(), Intrinsic::pa_pacia);

  if (paced == nullptr) {
    auto VInput = SI->getValueOperand();
    auto VOutput = SI->getPointerOperand();
    auto VInputType = VInput->getType();

    if (VInputType->isStructTy()) {
      auto VInputStruTy = dyn_cast<StructType>(VInputType);
      if (isa<Constant>(VInput)) {
        IRBuilder<> Builder(I.getNextNode());
        auto CV = dyn_cast<Constant>(VInput);
        for (unsigned i = 0; i < VInputStruTy->getNumElements(); ++i) {
          auto elemCV = CV->getAggregateElement(i);
          if (isa<PtrToIntOperator>(elemCV)) {
            auto elemTy = dyn_cast<PtrToIntOperator>(elemCV)
                              ->getPointerOperand()
                              ->getType();
            if (elemTy->isPointerTy() &&
                elemTy->getPointerElementType()->isFunctionTy()) {
              auto loaded = Builder.CreateLoad(elemTy, VOutput);
              auto paced =
                  createPACIntrinsic(&Builder, *(F.getParent()), loaded,
                                     loaded->getType(), Intrinsic::pa_pacia);
              Builder.CreateStore(paced, VOutput);
            }
          }
        }
      }
    }
    return regenPACedValue(F, I, SI->getValueOperand(), Intrinsic::pa_pacia);
  }

  SI->setOperand(0, paced);
  return true;
}

bool OptCpiPass::handleSelectInsn(Function &F, Instruction &I) {
  auto retVal = false;

  for (unsigned int i = 0; i < I.getNumOperands(); ++i) {
    auto paced = genPACedValue(F, I, I.getOperand(i), Intrinsic::pa_pacia);
    if (paced != nullptr) {
      retVal = true;
      I.setOperand(i, paced);
    } else {
      retVal |= regenPACedValue(F, I, I.getOperand(i), Intrinsic::pa_pacia);
    }
  }

  return retVal;
}

bool OptCpiPass::handleCallInsn(Function &F, Instruction &I,
                                const TargetLibraryInfo *TLI) {
  auto CI = dyn_cast<CallInst>(&I);
  auto calledFunc = CI->getCalledFunction();
  LibFunc Func;
  bool isLibFn = false;
  static Function *funcAutVTablePara = nullptr, *funcSignVTablePara = nullptr,
                  *funcSignDlsym = nullptr;
  auto M = F.getParent();
  auto &C = M->getContext();
  Type *voidTy = Type::getVoidTy(C);
  Type *int64Ty = Type::getInt64Ty(C);

#if CHECK_PAC_BEFORE_AUT == 1
  static Function *funcAutFP = nullptr;
#endif

  // if the call is a virtual member function call, we do not replace
  // br/blr by braa/blraa.
  if (CI->hasMetadata("pac_disabled")) {
    outs() << getPassName() << ": pac disabled\n";
    goto handle_args;
  }

  // Handle indirect call
  if (CI->isIndirectCall()) {
    auto calledValue = CI->getCalledOperand();

    // Handle bitcast
    auto calledValueType =
        isa<BitCastOperator>(calledValue)
            ? dyn_cast<BitCastOperator>(calledValue)->getDestTy()
            : calledValue->getType();

    /* DEBUG(outs() << getPassName() */
    /*              << ": called type = " << *(CI->getFunctionType()) << '\n');
     */
    /* DEBUG(outs() << getPassName() << ": called value = " << *calledValue */
    /*              << '\n'); */

    if (isa<PHINode>(calledValue)) {
      auto incoming = dyn_cast<PHINode>(calledValue)->getIncomingValue(1);
      if (isa<IntToPtrInst>(incoming) && !isa<LoadInst>(incoming)) {
        auto ITP = dyn_cast<IntToPtrInst>(incoming);
        auto BB = ITP->getParent();
        auto lastInst = BB->getTerminator();
        IRBuilder<> Builder(lastInst);
        auto autcall = Intrinsic::getDeclaration(M, Intrinsic::pa_autia,
                                                 {ITP->getDestTy()});
        auto mod = Constant::getIntegerValue(
            Type::getInt64Ty(F.getContext()),
            APInt(64, getTypeIDFor(ITP->getDestTy())));
        auto auted = Builder.CreateCall(autcall, {ITP, mod}, "");
        dyn_cast<PHINode>(calledValue)->setIncomingValue(1, auted);
        goto handle_args;
      }
    }
#if CHECK_PAC_BEFORE_AUT == 1
    if (!funcAutFP) {
      std::vector<Type *> args(2, int64Ty);
      FunctionType *prototype = FunctionType::get(int64Ty, args, false);
      funcAutFP = Function::Create(prototype, Function::PrivateLinkage,
                                   "__pac_aut_fp", M);

      funcAutFP->addFnAttr("no-pac", "true");
      funcAutFP->addFnAttr("noinline", "true");

      auto BB = BasicBlock::Create(C, "entry", funcAutFP);
      IRBuilder<> BuilderAutEntry(BB);

      auto stripped = BuilderAutEntry.CreateAnd(
          funcAutFP->getArg(0), ConstantInt::get(int64Ty, 0xffff000000000000));
      auto cmp =
          BuilderAutEntry.CreateICmpEQ(stripped, ConstantInt::get(int64Ty, 0));

      auto autBB = BasicBlock::Create(C, "aut", funcAutFP);
      auto retBB = BasicBlock::Create(C, "ret", funcAutFP);
      BuilderAutEntry.CreateCondBr(cmp, retBB, autBB);

      IRBuilder<> BuilderAut(autBB);
      IRBuilder<> BuilderRet(retBB);

      auto autcall = Intrinsic::getDeclaration(
          M, Intrinsic::pa_autia, {funcAutFP->getArg(0)->getType()});
      auto auted = BuilderAut.CreateCall(
          autcall, {funcAutFP->getArg(0), funcAutFP->getArg(1)}, "");

      BuilderAut.CreateRet(auted);
      BuilderRet.CreateRet(funcAutFP->getArg(0));
    }

    IRBuilder<> BuilderBefore(&I);
    auto mod =
        Constant::getIntegerValue(Type::getInt64Ty(F.getContext()),
                                  APInt(64, getTypeIDFor(calledValueType)));

    auto autFpCI = BuilderBefore.CreateCall(funcAutFP, {calledValue, mod});

    CI->setCalledOperand(autFpCI);
#else
    auto paced = createPACIntrinsic(F, I, calledValue, calledValueType,
                                    Intrinsic::pa_autcall);
    CI->setCalledOperand(paced);
#endif
  }

handle_args:
  // handle externel function call
  if (calledFunc != nullptr) {
    if (isSkippedFuncs(calledFunc->getName())) {
      /* DEBUG(outs() << getPassName() << ": skip " << calledFunc->getName() */
      /*              << '\n'); */
      goto out;
    }

    if (TLI)
      isLibFn = TLI->getLibFunc(calledFunc->getName(), Func);

    if (isLibFn || calledFunc->getName().contains("pthread")) {
      // authenticate args which are code pointers
      for (unsigned int i = 0; i < CI->arg_size(); ++i) {
        auto arg = CI->getArgOperand(i);
        const auto argTy = arg->getType();

        if (argTy->isPointerTy() &&
            argTy->getPointerElementType()->isFunctionTy() &&
            !isa<Function>(arg) && !isa<Constant>(arg)) {
          auto VInput = isa<BitCastOperator>(arg)
                            ? dyn_cast<BitCastOperator>(arg)->getOperand(0)
                            : arg;
          auto VTypeInput = isa<BitCastOperator>(arg)
                                ? dyn_cast<BitCastOperator>(arg)->getSrcTy()
                                : arg->getType();
          auto paced =
              createPACIntrinsic(F, I, VInput, VTypeInput, Intrinsic::pa_autia);
          CI->setArgOperand(i, paced);
        }
      }
    } else if (calledFunc->getName().contains("sigaction")) {
      auto arg = dyn_cast<CallInst>(&I)->getArgOperand(1);
      const auto argTy =
          dyn_cast<StructType>(arg->getType()->getPointerElementType());

      IRBuilder<> BuilderBefore(&I);
      IRBuilder<> BuilderAfter(I.getNextNode());

      std::vector<Type *> args(1, int64Ty);
      FunctionType *prototype = FunctionType::get(voidTy, args, false);
      Function *funcAut =
          Function::Create(prototype, Function::PrivateLinkage, "__pac_aut", M);

      funcAut->addFnAttr("no-pac", "true");
      funcAut->addFnAttr("noinline", "true");

      auto BB = BasicBlock::Create(C, "entry", funcAut);
      IRBuilder<> BuilderAutEntry(BB);

      Function *funcSign = Function::Create(prototype, Function::PrivateLinkage,
                                            "__pac_sign", M);
      funcSign->addFnAttr("no-pac", "true");
      funcSign->addFnAttr("noinline", "true");
      BB = BasicBlock::Create(C, "entry", funcSign);
      IRBuilder<> BuilderSignEntry(BB);

      /* DEBUG(outs() << "Value: " << *arg << '\n'); */
      /* DEBUG(outs() << "Type: " << *argTy << "\n"); */
      assert(argTy != nullptr);

      for (auto i = 0U; i < argTy->getNumElements(); ++i) {
        auto elementTy = argTy->getElementType(i);
        /* DEBUG(outs() << "Element Type: " << *elementTy << '\n'); */

        if (elementTy->isStructTy()) { // union __sigaction_handler
          Type *intraElementTy =
              dyn_cast<StructType>(elementTy)->getElementType(0);
          /* DEBUG(outs() << "Intra Element Type: " << *intraElementTy << "\n");
           */

          if (intraElementTy->isPointerTy() &&
              intraElementTy->getPointerElementType()->isFunctionTy()) {
            auto elementPtr = BuilderBefore.CreateStructGEP(argTy, arg, i);
            BuilderBefore.CreateCall(funcAut, {elementPtr});

            LoadInst *loaded =
                BuilderAutEntry.CreateLoad(intraElementTy, funcAut->getArg(0));
            // Check if sa_handler is SIG_DFL/SIG_IGN
            Value *cmp = BuilderAutEntry.CreateICmpUGT(
                loaded, ConstantInt::get(Type::getInt64Ty(C), 2));
            auto autBB = BasicBlock::Create(C, "aut", funcAut);
            auto retBB = BasicBlock::Create(C, "ret", funcAut);
            BuilderAutEntry.CreateCondBr(cmp, autBB, retBB);

            IRBuilder<> BuilderAut(autBB);
            IRBuilder<> BuilderRet(retBB);

            loaded = BuilderAut.CreateLoad(intraElementTy, funcAut->getArg(0));

            // Insert PAC intrinsic
            auto auted =
                createPACIntrinsic(&BuilderAut, *(F.getParent()), loaded,
                                   voidTy, Intrinsic::pa_autia);

            BuilderAut.CreateStore(auted, funcAut->getArg(0));
            BuilderAut.CreateRetVoid();
            BuilderRet.CreateRetVoid();

            elementPtr = BuilderAfter.CreateStructGEP(argTy, arg, i);
            BuilderAfter.CreateCall(funcSign, {elementPtr});

            loaded = BuilderSignEntry.CreateLoad(intraElementTy,
                                                 funcSign->getArg(0));
            // Check if sa_handler is SIG_DFL/SIG_IGN
            cmp = BuilderSignEntry.CreateICmpUGT(
                loaded, ConstantInt::get(Type::getInt64Ty(C), 2));
            auto signBB = BasicBlock::Create(C, "sign", funcSign);
            retBB = BasicBlock::Create(C, "ret", funcSign);
            BuilderSignEntry.CreateCondBr(cmp, signBB, retBB);

            IRBuilder<> BuilderSign(signBB);
            IRBuilder<> BuilderSignRet(retBB);

            loaded =
                BuilderSign.CreateLoad(intraElementTy, funcSign->getArg(0));

            auto paced =
                createPACIntrinsic(&BuilderSign, *(F.getParent()), loaded,
                                   voidTy, Intrinsic::pa_pacia);
            BuilderSign.CreateStore(paced, funcSign->getArg(0));
            BuilderSign.CreateRetVoid();
            BuilderSignRet.CreateRetVoid();
          }
        }
      }
    } else if (calledFunc->getName().equals("__dynamic_cast") ||
               calledFunc->getName().contains("basic_streambuf")) {
      IRBuilder<> BuilderBefore(&I);
      IRBuilder<> BuilderAfter(I.getNextNode());

      auto arg = CI->getArgOperand(0);
      if (!funcAutVTablePara && !funcSignVTablePara) {
        std::vector<Type *> args(1, int64Ty);
        FunctionType *prototype = FunctionType::get(voidTy, args, false);
        funcAutVTablePara = Function::Create(
            prototype, Function::PrivateLinkage, "__pac_aut_vtable_para", M);

        funcAutVTablePara->addFnAttr("no-pac", "true");
        funcAutVTablePara->addFnAttr("noinline", "true");

        auto BB = BasicBlock::Create(C, "entry", funcAutVTablePara);
        IRBuilder<> BuilderAutEntry(BB);

        LoadInst *loaded =
            BuilderAutEntry.CreateLoad(funcAutVTablePara->getArg(0)->getType(),
                                       funcAutVTablePara->getArg(0));
        auto stripped = BuilderAutEntry.CreateAnd(
            loaded, ConstantInt::get(int64Ty, 0xffff000000000000));
        auto cmp = BuilderAutEntry.CreateICmpEQ(stripped,
                                                ConstantInt::get(int64Ty, 0));

        auto autBB = BasicBlock::Create(C, "aut", funcAutVTablePara);
        auto retBB = BasicBlock::Create(C, "ret", funcAutVTablePara);
        BuilderAutEntry.CreateCondBr(cmp, retBB, autBB);

        IRBuilder<> BuilderAut(autBB);
        IRBuilder<> BuilderRet(retBB);

        auto autcall = Intrinsic::getDeclaration(M, Intrinsic::pa_autia,
                                                 {loaded->getType()});
        auto auted = BuilderAut.CreateCall(
            autcall, {loaded, funcAutVTablePara->getArg(0)}, "");
        BuilderAut.CreateStore(auted, funcAutVTablePara->getArg(0));

        BuilderAut.CreateRetVoid();
        BuilderRet.CreateRetVoid();

        funcSignVTablePara = Function::Create(
            prototype, Function::PrivateLinkage, "__pac_sign_vtable_para", M);

        funcSignVTablePara->addFnAttr("no-pac", "true");
        funcSignVTablePara->addFnAttr("noinline", "true");

        BB = BasicBlock::Create(C, "entry", funcSignVTablePara);
        IRBuilder<> BuilderSignEntry(BB);

        loaded = BuilderSignEntry.CreateLoad(
            funcSignVTablePara->getArg(0)->getType(),
            funcSignVTablePara->getArg(0));
        stripped = BuilderSignEntry.CreateAnd(
            loaded, ConstantInt::get(int64Ty, 0xffff000000000000));
        cmp = BuilderSignEntry.CreateICmpEQ(stripped,
                                            ConstantInt::get(int64Ty, 0));
        auto signBB = BasicBlock::Create(C, "sign", funcSignVTablePara);
        retBB = BasicBlock::Create(C, "ret", funcSignVTablePara);
        BuilderSignEntry.CreateCondBr(cmp, retBB, signBB);

        IRBuilder<> BuilderSign(signBB);
        IRBuilder<> BuilderSignRet(retBB);

        autcall = Intrinsic::getDeclaration(M, Intrinsic::pa_pacia,
                                            {loaded->getType()});
        auto paced = BuilderSign.CreateCall(
            autcall, {loaded, funcSignVTablePara->getArg(0)}, "");
        BuilderSign.CreateStore(paced, funcSignVTablePara->getArg(0));

        BuilderSign.CreateRetVoid();
        BuilderSignRet.CreateRetVoid();
      }

      BuilderBefore.CreateCall(funcAutVTablePara, {arg});
      BuilderAfter.CreateCall(funcSignVTablePara, {arg});
    } else if (calledFunc->getName().contains("dlsym")) {
      outs() << getPassName() << ": little bitch\n";
      Instruction *str = &I;

      do {
        str = str->getNextNode();
        outs() << getPassName() << ": " << *str << '\n';
      } while (!isa<StoreInst>(str));
      outs() << getPassName() << ": " << *str->getOperand(0)->getType() << '\n';

      if (!funcSignDlsym) {
        std::vector<Type *> args(2, int64Ty);
        FunctionType *prototype = FunctionType::get(int64Ty, args, false);
        funcSignDlsym = Function::Create(prototype, Function::PrivateLinkage,
                                         "__pac_sign_", M);

        funcSignDlsym->addFnAttr("no-pac", "true");
        funcSignDlsym->addFnAttr("inline", "true");
        auto BB = BasicBlock::Create(C, "entry", funcSignDlsym);
        IRBuilder<> BuilderSignEntry(BB);

        auto cmp = BuilderSignEntry.CreateICmpEQ(funcSignDlsym->getArg(0),
                                                 ConstantInt::get(int64Ty, 0));

        auto signBB = BasicBlock::Create(C, "sign", funcSignDlsym);
        auto retBB = BasicBlock::Create(C, "ret", funcSignDlsym);
        BuilderSignEntry.CreateCondBr(cmp, retBB, signBB);

        IRBuilder<> BuilderSign(signBB);
        IRBuilder<> BuilderRet(retBB);

        auto autcall = Intrinsic::getDeclaration(
            M, Intrinsic::pa_pacia, {funcSignDlsym->getArg(0)->getType()});
        auto paced = BuilderSign.CreateCall(
            autcall, {funcSignDlsym->getArg(0), funcSignDlsym->getArg(1)}, "");

        BuilderSign.CreateRet(paced);
        BuilderRet.CreateRet(funcSignDlsym->getArg(0));
      }

      IRBuilder<> Builder(str);
      /* auto loaded = */
      /*     Builder.CreateLoad(str->getOperand(0)->getType(),
       * str->getOperand(0)); */
      auto mod = Constant::getIntegerValue(
          Type::getInt64Ty(F.getContext()),
          APInt(64, getTypeIDFor(str->getOperand(0)->getType())));
      auto sign = Builder.CreateCall(
          funcSignDlsym, {str->getOperand(0), mod});
      str->setOperand(0, sign);
    } else {
      // sign args which are code pointers
      for (unsigned int i = 0; i < CI->arg_size(); ++i) {
        auto arg = CI->getArgOperand(i);
        auto paced = genPACedValue(F, I, arg, Intrinsic::pa_pacia);
        if (paced != nullptr)
          CI->setArgOperand(i, paced);
      }
    }
  } else {
    // sign args which are code pointers
    for (unsigned int i = 0; i < CI->arg_size(); ++i) {
      auto arg = CI->getArgOperand(i);
      auto paced = genPACedValue(F, I, arg, Intrinsic::pa_pacia);
      if (paced != nullptr)
        CI->setArgOperand(i, paced);
    }
  }

out:
  return true;
}

bool OptCpiPass::handleInvokeInsn(Function &F, Instruction &I) {
  auto II = dyn_cast<InvokeInst>(&I);
  auto calledFunc = II->getCalledFunction();
  unsigned argsz = II->arg_size();

  if (calledFunc && isSkippedFuncs(calledFunc->getName())) {
    DEBUG(outs() << getPassName() << ": skip" << calledFunc->getName() << '\n');
    goto out;
  }

  for (unsigned i = 0; i < argsz; ++i) {
    auto arg = II->getArgOperand(i);
    auto paced = genPACedValue(F, I, arg, Intrinsic::pa_pacia);
    if (paced != nullptr)
      II->setArgOperand(i, paced);
  }

out:
  return true;
}

CallInst *OptCpiPass::genPACedValue(Function &F, Instruction &I, Value *V,
                                    Intrinsic::ID intrinsicID) {
  // We need to handle two types of function pointer arguments:
  // 1) a direct function
  // 2) a direct function passed via BitCastOperator
  auto VTypeInput = (isa<BitCastOperator>(V) && dyn_cast<BitCastOperator>(V)
                                                    ->getDestTy()
                                                    ->getPointerElementType()
                                                    ->isIntegerTy())
                        ? dyn_cast<BitCastOperator>(V)->getSrcTy()
                        : V->getType();
  auto VInput = (isa<BitCastOperator>(V))
                    ? dyn_cast<BitCastOperator>(V)->getOperand(0)
                    : V;

  /* DEBUG(outs() << getPassName() << ": " << *VTypeInput << '\n'); */
  /* DEBUG(outs() << getPassName() << ": " << *VInput << '\n'); */

  // We can skip if the operand is not function address
  if (!VTypeInput->isPointerTy() || !isa<Function>(VInput) ||
      dyn_cast<Function>(VInput)->isIntrinsic())
    return nullptr;

  // V->getType and VTypeInput should match unless bitcast
  assert((isa<BitCastOperator>(V) || V->getType() == VTypeInput));


  // Create PA intrinsic (pacia)
  /* DEBUG(outs() << getPassName() << ":\n\t" << F.getName() */
  /*        << ":\n\t" << I << '\n' */
  /*        << "Create pacia intrinsic here\n"); */

  if (isa<StoreInst>(&I)) {
    auto dest = dyn_cast<StoreInst>(&I)->getPointerOperand();
    if (isa<BitCastOperator>(dest)) {
      auto src = dyn_cast<BitCastOperator>(dest)->getOperand(0);
      if (isa<GetElementPtrInst>(src)) {
        auto srcTy = dyn_cast<GetElementPtrInst>(src)->getSourceElementType();
        if (isa<StructType>(srcTy)) {
          auto SName = dyn_cast<StructType>(srcTy)->getStructName();
          if (SName.contains("sigaction")) {
            VTypeInput = Type::getVoidTy(F.getContext());
          }
        }
      }
    }
  }

  // Workaround(Apache httpd)
  if (isa<CallInst>(&I)) {
    auto CI = dyn_cast<CallInst>(&I);
    auto calledFunc = CI->getCalledFunction();
    if (calledFunc && calledFunc->getName().contains("apr_signal"))
      VTypeInput = Type::getVoidTy(F.getContext());
  }

  /* DEBUG(outs() << getPassName() << ": Need PAC\n"); */
  return createPACIntrinsic(F, I, V, VTypeInput, intrinsicID);
}

bool OptCpiPass::regenPACedValue(Function &F, Instruction &I, Value *V,
                                 Intrinsic::ID intrinsicID) {
  /* DEBUG(outs() << *V << '\n'); */
  if (!isa<BitCastOperator>(V) || dyn_cast<BitCastOperator>(V)
                                      ->getDestTy()
                                      ->getPointerElementType()
                                      ->isIntegerTy())
    // void *
    return false;

  auto VTypeInput = dyn_cast<BitCastOperator>(V)->getSrcTy();
  auto VInput = dyn_cast<BitCastOperator>(V)->getOperand(0);

  if (!VTypeInput->isPointerTy() ||
      !VTypeInput->getPointerElementType()->isFunctionTy())
    return false;

  /* DEBUG(outs() << getPassName() << ":\n" << I */
  /*        << "\nre-generate PAC\n"); */

  auto nextI = I.getNextNode();
  auto BB = nextI->getParent();                // BB before and contains store
  auto successor = BB->splitBasicBlock(nextI); // BB after store
  auto newBB = BasicBlock::Create(F.getContext(), "rePAC", &F);
  auto lastInst = BB->getTerminator();

  lastInst->eraseFromParent();

  IRBuilder<> Builder(BB);

  // check nullptr
  Value *cmp = Builder.CreateICmpEQ(
      VInput, ConstantInt::get(Type::getInt64Ty(F.getContext()), 0));
  Builder.CreateCondBr(cmp, successor, newBB);

  IRBuilder<> Builder2(newBB);

  Value *unpaced =
      Builder2.CreateAnd(VInput, APInt(64, 281474976710655)); // 48-bits

  auto paced = createPACIntrinsic(&Builder2, *(F.getParent()), unpaced,
                                  dyn_cast<BitCastOperator>(V)->getDestTy(),
                                  Intrinsic::pa_pacia);

  Builder2.CreateStore(paced, dyn_cast<StoreInst>(&I)->getPointerOperand());
  Builder2.CreateBr(successor);

  return true;
}

bool OptCpiPass::isSkippedFuncs(const StringRef &funcName) {
  for (const std::string &skippedFunc : skippedFunctions) {
    if (funcName.contains(skippedFunc)) {
      return true;
    }
  }
  return false;
}
