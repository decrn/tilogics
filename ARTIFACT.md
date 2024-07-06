# OOPSLA 2024 Artifact

Paper: Type Inference Logics

## Introduction

This artifact contains the supplementary code to our paper titled Type Inference Logics.
The code is comprised of two parts:

* a Coq formalization of the techniques discussed in the paper, and
* a small Haskell implementation (parser and printer) of the STLC with booleans that uses extracted code from the Coq formalization.

The latter is able to parse example programs, check/infer/elaborate them using the extracted Coq code, and pretty-print the final result.

The different parts can be found in the following directories

| Part                            | Directory                                  |
|---------------------------------|--------------------------------------------|
| Coq Formalization               | `em/theories`                              |
| Haskell implementation          | `em/src`                                   |
| Example programs                | `em/examples`                              |

We take special care to document source code using comments and use an extensible project layout that favours reusability whenever possible.

Please refer to the sections below in this document for detailed navigation of the code.
We provide a docker image with all the dependencies pre-installed, however, to read the code itself, we propose loading it into your preferred code editor locally.

## Hardware dependencies

This artifact can be evaluated on commodity hardware.
The code has been tested on both AMD64 and M1/M2 laptops.

## Getting started

### Get started with Docker

We have prepared a prebuilt Docker image containing the necessary software. If you prefer manual installation, see the next section below.

Proceed by downloading the prebuilt image tarball and running it with Docker:

```bash
docker load < tilogics-oopsla24-image.tar-gz
docker run -it --rm tilogics/oopsla24
```

### Get started without Docker

We strongly recommend the supplied prebuilt Docker image. Nevertheless, for manual installation, you can follow these steps.

You will need both OCaml (with opam) and Haskell (with cabal).

Proceed by creating a fresh opam switch,
pinning the Coq and Iris versions and installing `equations`, then, `stdpp` will be installed as a dependency of Iris:

```bash
opam switch create em ocaml-base-compiler.4.14.1
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq 8.17.1
opam pin add coq-iris 4.1.0
opam install coq-equations
```
b
To compile the Haskell code you will need ghc (tested with v9.0) and the `optparse-applicative` (tested with v0.16) and `parsec` (tested with v3.1) libraries.
These can will be installed automatically as dependencies when compiling our code with `cabal-install`.

### Compiling the code

Note for macOS users: you might need to install a version of GNU utils and use `gmake`.

- After that you can compile the Coq code by calling `make` in the root directory.
- You can extract the Coq code to Haskell by running `make extract` in the root directory.
- You can compile and run the extracted code on an example by running `cabal run em examples/two-bit-adder.stlcb` in the root directory.

### Functional Claim 1: Full separation of constraint generation and solving

In the paper we claim that we formalized a constraint-based type inference algorithm that fully separates (logically) constraint generation from solving.

In particular `theories/Monad/Interface.v` defines a type class `TypeCheckM` that defines an interface for a constraint generation monad.
Said interface 

Three instances of this monad are then derived:
* `theories/Monad/Free.v` using the Free monad discussed in §3.1;
* `theories/Monad/Prenex.v`, discussed in §3.4; and
* `theories/Monad/Solved.v`, discussed in §3.5. This instance is by far the most performant.

### Functional Claim 2: Executable through Code Extraction to Haskell

In the paper we claim that we can extract the Coq formalization to Haskell, thereby showing that our approach is directly executable.

To get started, see below. In essence, a user can run `make extract` which employs Coq's code extraction facility to compile a number of functions from the formalization to Haskell and applies a patch to the Haskell project under the `src/` directory.


The specific functions that are extracted from Coq can be found in `theories/Extraction.v:45`.
Coq extracts those functions and all their (recursive) dependencies. 
In summary, we extract all the necessary code to run the end-to-end `reconstruct` function from section 3.6
for all three monad instances (in the Coq formalization, this code can be found under `theories/Composition.v`, lines 65-89).

We augment the extracted Coq code with a (tiny, non-verified) parser for a surface syntax of
the STLCB and a (tiny, non-verified) pretty printer.

The relevant code can be found in the `src` subdirectory. To run it, first invoke Coq's extraction facilities
using `make extract` in the root directory. Then, use e.g. `cabal` to run one of the example programs from
the `examples/` directory:

```
make extract
cabal run em -- --solved examples/two-bit-adder.stlcb
```

The result is a type-reconstructed program, that was type checked and subsequently elaborated using the Solved monad from the type class discussed in Claim 1 above.

See also the section on Benchmarking below for a more detailed account of how to run our synthetic benchmark.

### Functional Claim 3: Fully Mechanized without Axioms or Unproven Assumptions

In the paper we claim that our Coq development does not rely on additional axioms or unproven assumptions.

This can be confirmed by printing with the
Coq command [`Print Assumptions`](https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#coq:cmd.Print-Assumptions).

Note that by running `make`, a file `theories/Assumptions.v` is automatically type checked and compiled by Coq that will print any
axioms or unproven assumptions in each of the parts of the code. The stdout of `make` should therefore include the following:

```txt
COQC theories/Assumptions.v
Assumptions of check generator correctness:
Closed under the global context
Assumptions of synth generator correctness:
Closed under the global context
Assumptions of bidirectional generator correctness:
Closed under the global context
Assumptions of end-to-end correctness:
Closed under the global context
Assumptions of decidability of typing :
Closed under the global context
```

## Mechanized formalization (Coq)

The primary artifact is a Coq project that implements the technical machinery discussed in the paper.

The following tables relate concepts discussed in the paper to specific code in the Coq development.

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

## Benchmarking

In order to benchmark the performance of the extracted code, we provide a small synthetic benchmark that infers (and elaborates) the types
of increasingly larger Church numerals and (possibly) worst-case terms.

The scripts to generate these terms can be found in the `util` directory. We have already generated these increasingly large Church numerals and worst-case terms. They can be found in the `examples/` directory besides other -- more realistic -- example programs.

To run the benchmark, it is sufficient to run `make bench`, provided that Coq compilation, extraction and Haskell compilation have succeeded. This make target will invoke `hyperfine`.
The result of the benchmark can then be found in the `bench/` directory. Each run will produce a short markdown summary of the execution times together with some small statistics.


