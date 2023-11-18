add_llvm_library( OptCpiPass
	OptCpiPass.cpp
	OptUtil.cpp

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

	LINK_LIBS
	LLVMCore
	LLVMSupport
	LLVMTransformUtils
	LLVMCodeGen
	)

set_property(TARGET OptCpiPass PROPERTY LLVM_SYSTEM_LIBS)
