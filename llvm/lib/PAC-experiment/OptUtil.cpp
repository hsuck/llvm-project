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
  auto paced = Builder.CreateCall(autcall, {calledValue, modifier}, "");

  return paced;
}
