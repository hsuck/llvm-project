add_llvm_library(sha3
    sha3.c
		platform_util.c

    ADDITIONAL_HEADER_DIRS
    ${LLVM_MAIN_INCLUDE_DIR}/llvm/SHA3/include
    )

	set_property(TARGET OptCpiPass PROPERTY LLVM_SYSTEM_LIBS)
