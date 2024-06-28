# Type Inference Logics

This document contains a brief explanation of the supplementary material that we
include as part of the paper submission. We intend to supply a more thorough
overview for the artifact submission.

## Overview

The supplementary material of our paper consists of two parts:

* a Coq project containing a mechanization of the techniques discussed in the paper
* a relatively small Haskell implementation of the simply typed lambda calculus with Booleans that utilizes extracted code from the mechanization

The different parts can be found in the following directories

| Part                            | Directory                                  |
|---------------------------------|--------------------------------------------|
| Coq Formalization               | `em/theories`                        |
| Haskell implementation          | `em/src`                             |


## Build instructions

An easy way to setup your system is to create a fresh opam switch,
pin the Coq and Iris versions and install equations
(stdpp will be installed as a dependency of Iris):

```
opam switch create em ocaml-base-compiler.4.14.1
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq 8.18.0
opam pin add coq-iris 4.1.0
opam install coq-equations
```

After that you can build the code by calling `make` in the root directory.

Note for macOS users: you might need to install a version of GNU utils and use `gmake`.

## Mechanized formalization (Coq)

The following tables relates concepts discussed in the paper to specific code in the Coq development.

The assumptions, i.e. unimplemented or unproven parts, can be printed with the
Coq command [`Print Assumptions`](https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#coq:cmd.Print-Assumptions).

### Section 2: Overview

| Concept   | Description                                 | Location in code               |
|-----------|---------------------------------------------|--------------------------------|
| Figure 1  | Simply typed lambda calculus with Booleans  | `Spec.v:75`                    |
| Figure 2  | Declarative typing and elab rules for STLCB | `Spec.v:92`                    |
| Figure 4  | Monad Def of Cstr w semantic values         | `Shallow/Monad/Interface.v:66` |
| Figure 5  | Monadic cstr gen w synth & elab             | `Shallow/Gen/Synthesise.v:92`  |
| Figure 6  | Free monad definition                       | `Shallow/Monad/Free.v:45`      |
| Figure 7  | Weakest Pres for the Free monad             | `Shallow/Monad/Free.v:89`      |
| Figure 8  | Weakest Liberal Pres for the Free monad     | `Shallow/Monad/Free.v:98`      |

### Section 3: Monadic constraint generation

| Concept   | Description                                 | Location in code        |
|-----------|---------------------------------------------|-------------------------|
| Figure 9  | World-indexed types                         | `Worlds.v:207`          |
| Figure 10 | Definition of the Free monad                | `Monad/Free.v:37`       |
| Figure 11 | Parellel substitutions                      | `Sub/Parallel.v`        |
| Figure 12 | Notations                                   | `Worlds.v:310`          |
| Figure 13 | Free monad bind                             | `Monad/Free.v:49`       |
| Figure 14 | Monadic interface for constraint generation | `Monad/Interface.v:65`  |
| Figure 15 | The Open modality and applicative interface | `Open.v`                |
| N/A       | do-notation                                 | `Monad/Interface.v:50`  |
| Figure 16 | Constraint generator for synth + elab       | `Gen/Synthesise:47`     |
| N/A       | Smart constructors for STLCB                | `Open.v:124`            |
| N/A       | prenex function                             | `PrenexConversion.v:34` |
| N/A       | solve function                              | `Unification.v:180`     |
| N/A       | run function                                | `Composition.v:40`      |
| N/A       | reconstruct function                        | `Composition.v:63`      |


### Section 4: Type inference logics

| Concept             | Description                        | Location in code               |
|---------------------|------------------------------------|--------------------------------|
| Figure 17           | Closed alg. typing relation        | `Composition.v:72`             |
| Figure 18           | Assignment predicates              | `BaseLogic.v:54`               |
| Figure 19           | Substitution wp/wlp                | `BaseLogic.v:460`              |
| Figure 20           | Free WP/WLP                        | `Monad/Free.v:68`              |
| Figure 21           | Program logic interface for CstrM  | `Monad/Interface.v:81`         |
| Theorem 4.1         | End-to-end correctness             | `Composition.v:79`             |
| N/A                 | Open algorithmic typing relation   | `Gen/Synthesise.v:89`          |
| Theorem 4.2         | Generator correctness              | `Gen/Synthesise.v:231`         |
| Lemma 4.3           | Generator soundness                | `Gen/Synthesise.v:200`         |
| Lemma 4.4           | Generator completeness             | `Gen/Synthesise.v:219`         |
| Lemma 4.5           | Prenex conversion correctness      | `PrenexConversion.v:50`        |
| Lemma 4.6           | Constraint solver correctness      | `Unification.v:258`            |
| Corollary 4.7       | Decidability of typing             | `Composition.v:111`            |
| Figure 22           | Logical Relation                   | `Related/Monad/Interface.v:41` |
| Figure 23           | Logical Relation for Free          | `Related/Monad/Free.v:50`      |
| Lemma 4.8           | Relatedness of the generators      | `Related/Gen/Synthesise.v:83`  |
| Lemma 4.9           | Relatedness of WP                  | `Related/Monad/Free.v:83`      |
| Corollary 4.10      | Relatedness of algo typing         | `Related/Gen/Synthesise.v:91`  |
| Theorem 4.2 (again) | Generator correctness (via logrel) | `Related/Gen/Synthesise.v:103` |

## Haskell implementation

In this smaller artifact, we use Coq's extraction facilities to export results outside of the proof assistant.
In particular, we extract all the necessary code to run the end-to-end `reconstruct` function
from section 3.6 (in the Coq formalization, this code can be found under `theories/Composition.v`, lines 74-76).

We augment the extracted Haskell code with a (tiny, non-verified) parser for a surface syntax of
the STLCB and a (tiny, non-verified) pretty printer.

The relevant code can be found in the `src` subdirectory. To run it, first invoke Coq's extraction facilities
using `make extract` in the root directory. Then, use e.g. `cabal` to run one of the example programs from
the `examples/` directory:

```
make extract
cabal run em examples/full-adder.stlcb
```

The result is a type-reconstructed program.

