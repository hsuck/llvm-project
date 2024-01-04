// Author: hsuck

#include "llvm/PAC-experiment/OptUtil.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Type.h"
#include "llvm/PAC-experiment/PAC.h"
#include <map>
#include <regex>

#define USING_SHA3

extern "C" {
#include "../SHA3/mbedtls/sha3.h"
}

using namespace llvm;
using namespace llvm::PAC;

namespace {
std::map<const Type *, uint64_t> TypeIDCache;

void genTypeStr(const Type *T, raw_string_ostream &O) {
  /* outs() << __FUNCTION__ << '\n'; */
  switch (T->getTypeID()) {
  case Type::PointerTyID:
    /* outs() << "PointerTy\n"; */
    O << "ptr.";
    genTypeStr(T->getPointerElementType(), O);
    break;
  case Type::StructTyID: {
    /* outs() << "StructTy\n"; */
    auto name = dyn_cast<StructType>(T)->getStructName();
    std::regex expr("^(\\w+\\.\\w+)(\\.\\w+)?$");
    O << std::regex_replace(name.str(), expr, "$1") << ".";
    break;
  }
  case Type::ArrayTyID:
    /* outs() << "ArrayTy\n"; */
    O << "ptr.";
    genTypeStr(T->getArrayElementType(), O);
    break;
  case Type::FunctionTyID: {
    /* outs() << "FuncTy\n"; */
    auto funcTy = dyn_cast<FunctionType>(T);
    O << "f.";
    genTypeStr(funcTy->getReturnType(), O);

    for (auto param = funcTy->param_begin(); param != funcTy->param_end();
        ++param) {
      outs() << __FUNCTION__  << ":\tparamTy: " << **param << '\n';
      genTypeStr(*param, O);
    }
    break;
  }
  case Type::ScalableVectorTyID:
  case Type::FixedVectorTyID: {
    /* outs() << "VecTy\n"; */
    auto vecTy = dyn_cast<VectorType>(T);
    O << "vec." << vecTy->getElementCount();
    genTypeStr(vecTy->getElementType(), O);
    break;
  }
  case Type::VoidTyID:
    /* outs() << "VoidTy\n"; */
    O << "void.";
    break;
  default:
    assert(T->isIntegerTy() || T->isFloatingPointTy());
    /* outs() << "IntTy/FPTy\n"; */
    T->print(O);
    O << ".";
    break;
  }
}

uint64_t getTypeIDFor(const Type *T) {
  if (!T->isPointerTy())
    return 0;

  decltype(TypeIDCache)::iterator id = TypeIDCache.find(T);
  if (id != TypeIDCache.end())
    return id->second;

  uint64_t theTypeID = 0;
  std::string buf;
  raw_string_ostream typeStr(buf);

  genTypeStr(T, typeStr);
  typeStr.flush();

  outs() << "Type String: " << typeStr.str() << '\n';

  auto rawbuf = buf.c_str();
  mbedtls_sha3_context C;

  mbedtls_sha3_init(&C);

  auto *input = reinterpret_cast<const unsigned char *>(rawbuf);
  auto *output = new unsigned char[32]();

  auto result = mbedtls_sha3(MBEDTLS_SHA3_256, input, buf.length(), output, 32);
  if (result)
    llvm_unreachable("sha3 failed\n");
  memcpy(&theTypeID, output, sizeof(theTypeID));
  delete[] output;

  TypeIDCache.emplace(T, theTypeID);

  outs() << "Type ID: " << theTypeID << '\n';
  return theTypeID;
}
} // namespace

CallInst *OptUtil::createPACIntrinsic(Function &F, Instruction &I,
                                      Value *calledValue, Type *calledValueType,
                                      Intrinsic::ID intrinsicID) {
  // Generate Builder for inserting PA intrinsic
  IRBuilder<> Builder(&I);
  // Get PA intrinsic declaration for correct input type
  auto autcall = Intrinsic::getDeclaration(F.getParent(), intrinsicID,
                                           {calledValue->getType()});
  /* auto modifier = */
  /*      Constant::getIntegerValue(Type::getInt64Ty(F.getContext()), APInt(64, 0)); */
  auto modifier =
      Constant::getIntegerValue(Type::getInt64Ty(F.getContext()),
                                APInt(64, getTypeIDFor(calledValueType)));

  // Insert PAC intrinsic
  return Builder.CreateCall(autcall, {calledValue, modifier}, "");
}

Value *OptUtil::createPACIntrinsic(IRBuilder<> *builder, Module &M, Value *V,
                                   Type *T, Intrinsic::ID intrinsicID) {
  // Get PA intrinsic declaration for correct input type
  auto autcall = Intrinsic::getDeclaration(&M, intrinsicID, {V->getType()});
  /* auto modifier = */
  /*      Constant::getIntegerValue(Type::getInt64Ty(M.getContext()), APInt(64, 0)); */
  auto modifier = Constant::getIntegerValue(Type::getInt64Ty(M.getContext()),
                                            APInt(64, getTypeIDFor(T)));

  // Insert PAC intrinsic
  return builder->CreateCall(autcall, {V, modifier}, "");
}
