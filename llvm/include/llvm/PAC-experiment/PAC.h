// Author: hsuck

#ifndef LLVM_PAC_EXP_H
#define LLVM_PAC_EXP_H

#include "llvm/IR/Constant.h"
#include "llvm/IR/Type.h"
#include "llvm/Pass.h"

namespace llvm {

namespace PAC {

Pass *createOptCpiPass();

} // namespace PAC

} // namespace llvm
#endif // LLVM_PAC_EXP_H
