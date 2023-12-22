// Author: hsuck

#include "llvm/PAC-experiment/OptUtil.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Operator.h"
#include "llvm/PAC-experiment/PAC.h"

using namespace llvm;
using namespace llvm::PAC;

CallInst *OptUtil::createPACIntrinsic(Function &F, Instruction &I,
                                      Value *calledValue,
                                      Intrinsic::ID intrinsicID) {
  const auto calledValueType = calledValue->getType();
  // Generate Builder for inserting PA intrinsic
  IRBuilder<> Builder(&I);
  // Get PA intrinsic declaration for correct input type
  auto autcall =
      Intrinsic::getDeclaration(F.getParent(), intrinsicID, {calledValueType});
  auto modifier =
      Constant::getIntegerValue(Type::getInt64Ty(F.getContext()), APInt(64, 0));

  // Insert PAC intrinsic
  return Builder.CreateCall(autcall, {calledValue, modifier}, "");
}

Value *OptUtil::createPACIntrinsic(IRBuilder<> *builder, Module &M, Value *V,
                                   Intrinsic::ID intrinsicID) {
  const auto type = V->getType();
  // Get PA intrinsic declaration for correct input type
  auto autcall = Intrinsic::getDeclaration(&M, intrinsicID, {type});
  auto modifier =
      Constant::getIntegerValue(Type::getInt64Ty(M.getContext()), APInt(64, 0));

  // Insert PAC intrinsic
  return builder->CreateCall(autcall, {V, modifier}, "");
}
