# PQASM

PQASM is a high-assurance framework implemented with the Coq proof assistant, allowing us to certify our PQASM: a high-assurance framework implemented with the Coq proof assistant, allowing us to certify our PQASM tool to correctly reflect quantum program behaviors. 

## Overview

This repository contains the code used in our draft "Verified Compilation of Quantum Oracles," available [on arXiv](https://arxiv.org/pdf/2112.06700.pdf).

**Abstract**: One of the key steps in quantum algorithms is to prepare an initial quantum superposition state with different kinds of features. These so-called state preparation algorithms are essential to the behavior of quantum algorithms, and complicated state preparation algorithms are difficult to develop correctly and effectively. This paper presents Pqasm: a high-assurance framework implemented with the Coq proof assistant, allowing us to certify our Pqasm tool to correctly reflect quantum program behaviors. The key in the framework is to reduce the program correctness assurance of a program containing a quantum superposition state to the program correctness assurance for the program state without superposition. The reduction allows the development of an effective testing framework for testing quantum state preparation algorithm implementations on a classical computer -- considered to be a hard problem with no clear solution until this point. We utilize the QuickChick property-based testing framework to test state preparation programs. We evaluated the effectiveness of our approach over 5 case studies implemented using PQASM; such cases are not even simulatable in the current quantum simulators.

## Setup

To compile PQASM, you will need [Coq](https://coq.inria.fr/) and [QuickChick](https://github.com/QuickChick/QuickChick). We strongly recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Coq and `opam switch` to manage Coq versions. We currently support Coq **versions 8.13-8.14** and QuickChick **1.6.5**.

Assuming you have opam installed (following the instructions in the link above), follow the steps below to set up your environment.
```
# environment setup
opam init
eval $(opam env)

# install some version of the OCaml compiler in a switch named "pqasm"
opam switch create pqasm 4.12.0
eval $(opam env)

# install Coq -- this will take a while!
opam install coq

# install coq-quickchick
opam install coq-quickchick
```

*Notes*:
* Depending on your system, you may need to replace 4.12.0 in the instructions above with something like "ocaml-base-compiler.4.12.0". Any recent version of OCaml should be fine. 
* We have tested compilation with Coq versions 8.13.2 and 8.14.1.
* opam error messages and warnings are typically informative, so if you run into trouble then make sure you read the console output.

## Compiling & Running PQASM

Run `make` in the top-level directory to compile our Coq proofs. See the README in the experiments directory for information on how to run PQASM to generate the data in our paper.

## Directory Contents

PQASM
* PQASM.v -  PQASM language, semantics, and compilation from PQASM to SQIR.
* PTesting.v -  Data structures and theorems for PBT testing, as well as PBT testing results for quantum state preparation programs.

OQASM
* OQASM.v - OQASM language, type system, and compilation from OQASM to SQIR.
* OQASMProof.v - Proofs for the type soundness and the compilation correctness.
* CLArith.v - "Classical" arithmetic operations using X and CU gates.
* RZArith.v - Arithmetic operations using QFT/AQFT and z-axis rotations.

OQIMP
* OQIMP.v - OQIMP language, type system, and compilation from OQIMP to OQASM.
* OracleExample.v - Example oracles written in OQIMP including SHA224, ChaCha20, sin, cos, arcsin, x^n.
* Testing.v - Data structures and theorems for random testing for OQASM.
* ArithTesting.v - Random testing results for arithmetic operations.

Utilities
* BasicUtility.v - Useful helper functions and tactics.
* MathSpec.v - Abstract specifications for arithmetic operations.
* ExtrOQASM.v - Alternate definitions using a gate set suitable for extraction, including PQASM.

The `experiments` directory contains utilities for extracting PQASM code & running the experiments in our paper. See the README in that directory for more information.


