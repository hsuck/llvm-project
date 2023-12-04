// Author: hsuck

#include "llvm/Support/CommandLine.h"

// PAC-experiment
#include "llvm/PAC-experiment/PAC.h"

using namespace llvm;
using namespace llvm::PAC;

static cl::opt<bool> EnablePACFeCfi("pac-experiment", cl::NotHidden,
                               cl::desc("PAC forward-edge CFI"),
                               cl::init(false));

bool llvm::PAC::isPACFeCfi() {
	return EnablePACFeCfi;
}
