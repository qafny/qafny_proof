# Qafny to HILR Proof

We propose a translation proof from Qafny to HLIR.

## Overview

Verifying quantum programs today requires specialized proof systems built on interactive theorem provers such as Rocq, Lean, Isabelle, or Why3, and even modest quantum algorithms cost substantial human effort to verify. Because quantum programs cannot be effectively checked by runtime testing, formal verification is the only viable path to correctness, making the cost of these bespoke systems the chief barrier to scalable quantum software assurance. We show that verifying a quantum program should be no harder than verifying a classical array program, a paradigm commonly used in parallel programming: the Qafny quantum proof system embeds soundly and relatively completely into Hoare logic with array theory, and we mechanize soundness in Rocq. The embedding determinizes quantum proof obligations and exposes the full machinery of classical automated verifiers (e.g. Dafny and SMT-based separation logic) to quantum code, removing the need for dedicated quantum proof system infrastructure.

## Setup

To compile the project, you will need [Coq](https://coq.inria.fr/) and [QuickChick](https://github.com/QuickChick/QuickChick). We strongly recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Coq and `opam switch` to manage Coq versions. We currently support Coq **versions 8.16**.

Assuming you have opam installed (following the instructions in the link above), follow the steps below to set up your environment.
```
# environment setup
opam init
eval $(opam env)

# install some version of the OCaml compiler in a switch named "qnp"
opam switch create qnp 4.12.0
eval $(opam env)

# install Coq -- this will take a while!
opam install coq

# install coq-quickchick
opam install coq-quickchick
```
*Notes*:
* Depending on your system, you may need to replace 4.12.0 in the instructions above with something like "ocaml-base-compiler.4.12.0". Any recent version of OCaml should be fine. 
* We require Coq version >= 8.16.
* opam error messages and warnings are typically informative, so if you run into trouble then make sure you read the console output.

# install the QuantumLib library
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-quantumlib.1.7.0

# Optional, if you want to compile the proofs in examples/shor
opam install coq-interval
opam pin coq-euler https://github.com/taorunz/euler.git

# install the SQIR library
To install SQIR, run opam pin coq-sqir https://github.com/inQWIRE/SQIR.git

To pull subsequent updates, run opam install coq-sqir.

To import SQIR files, use Require Import SQIR.FILENAME


## Compiling & Running the Proof

Run `make` in the top-level directory to compile our Coq proofs. externals directory contains the coq files from SQIR and QWIRE that support the development of the soundness proof.
If you do not have a make file, please run `coq_makefile -f _CoqProject -o Makefile`

## Directory Contents

* QafnySyntax.v - The Qafny language syntax.
* LocusDef.v - Locus and state syntax and equation rules.
* LocusType.v - The Qafny Type system.
* LocusSem.v - The Qafny language semantics.
* LocusProof.v - The Qafny proof system.
* HoareLArray.v - The Hoare Logic and HLIR definition, as well as the soundness proof from Qafny to Hoare Logic for Theorem 6.14 with all the lemmas in Section 6, as well as Pureness theorem (Theorem 4.2) and Lemma 5.2.
* HoareLArrayComplete.v - The partially finished relatively completeness proof from Qafny to Hoare Logic for Theorem 6.15.


