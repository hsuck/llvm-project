// Author: hsuck

#ifndef __OPTUTIL_H__
#define __OPTUTIL_H__

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Type.h"

namespace llvm {
namespace PAC {
namespace OptUtil {
CallInst *createPACIntrinsic(Function &F, Instruction &I, Value *calledValue,
                             Intrinsic::ID intrinsicID);
Value *createPACIntrinsic(IRBuilder<> *builder, Module &M, Value *V);
} // namespace OptUtil
} // namespace PAC
} // namespace llvm
#endif // __OPTUTIL_H__
