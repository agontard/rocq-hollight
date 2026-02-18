# HOL-Light libraries in Rocq

This [Rocq](https://rocq-prover.org/) library contains an automatic translation of the [HOL-Light](https://github.com/jrh13/hol-light) libraries [Multivariate/make_complex.ml](https://github.com/jrh13/hol-light/blob/master/Multivariate/make_complex.ml) and [Logic/make.ml](https://github.com/jrh13/hol-light/blob/master/Logic/make.ml) with various HOL-Light types and functions mapped to the corresponding types and functions of the Rocq standard library or of the Mathcomp library.

## Contents
This repository tries to emulate the structure of the [HOL-Light repository](https://github.com/jrh13/hol-light), with additionnal subfolders for intermediary translations (intermediary translations allow to use HOL-Light theorems for key mappings, namely the type `real` and the `unify` function from the logic library).
- file init.v contains the alignments of pointed Types and HOL-Light connectives, axioms, and basic constructions like subtypes, along with a wide range of tactics useful for dealing with hol-light objects or proving specific kinds of alignments.
- file morepointedtypes.v is a makeshift fix of a problem with mathcomp's structure 
- **Real_With_N**: Basic alignments (basic types, functions on natural numbers and lists) with the Rocq standard library. The HOL-Light type `num` of natural numbers is mapped to the Rocq type `N` of binary natural numbers.
- A translation of Multivariate based on Real_With_N was made which aligned the type `real` and its operations with Rocq's standard library, but is not maintained and was based on an older version of Real_With_N.
- **Real_With_nat**: same as Real_With_N but `num` is mapped to the more common type `nat` of unary natural numbers, and functions on `num` and `list` are mapped to their Mathcomp counterparts.
- **HOL**: Translation of `hol_lib.ml` which is a common dependency of all other translated libraries, containing in particular the alignments of the types `real` and `int` (and functions on them) with their mathcomp counterparts.
- **Multivariate**: Translation of the Multivariate library based on mappings from **HOL** with additionnal mappings for vectors and topological spaces.
- **Unif**: Translation of part of the Logic library based on mappings from **HOL**, including the definition and alignment of the types of first order terms and formulae
- **Logic**: Translation of the Logic library based on **Unif**
- **Examples** and **Library**: respecting the structure of the HOL-Light repository, mappings of functions defined in files from either of these two directories are put here so that it is possible to use them for independent libraries which may all load these files and use these definitions.

## Building the libraries
dependencies can be installed via [opam](https://opam.ocaml.org/) with
```bash
$ opam repo add rocq-released https://rocq-prover.org/opam/released
$ opam install --deps-only .
```
The libraries can then be built with
```bash
$ make -j2
```
## Translated proofs
The translated theorems are provided as axioms in order to have a fast Require because the proofs currently extracted from HOL-Light are very big (91 Gb for Multivariate). The proofs can be retranslated and rechecked in a directory `./tmp/output` with the reproduce script. For more info, use it without arguments as such
```bash
$ ./reproduce
```
This script requires [opam](https://opam.ocaml.org/) to work.