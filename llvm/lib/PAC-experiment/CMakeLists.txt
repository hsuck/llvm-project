add_llvm_library( OptCpiPass
	OptCpiPass.cpp
	OptSignGlobalsPass.cpp
	OptUtil.cpp
	PAC.cpp

	ADDITIONAL_HEADER_DIRS
	${LLVM_MAIN_INCLUDE_DIR}/llvm/PAC-experiment
	${LLVM_MAIN_INCLUDE_DIR}/llvm/Support
	${LLVM_MAIN_INCLUDE_DIR}/llvm/IR

	DEPENDS
	intrinsics_gen
	LLVMCore
	LLVMSupport
	LLVMTransformUtils
	LLVMCodeGen
	sha3

	LINK_LIBS
	LLVMCore
	LLVMSupport
	LLVMTransformUtils
	LLVMCodeGen
	sha3
	)

set_property(TARGET OptCpiPass PROPERTY LLVM_SYSTEM_LIBS)
