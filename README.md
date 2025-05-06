# Lean Fuzzy Separation Logic
This repository features various contents about fuzzy and quantitative separation logic. It mainly focuses on fuzzy separation logic for concurrent and heap manipulating programs.

## Content
We provide the following:
1. semantics as Markov decision processes for concurrent probabilistic programs in `LeanFSL.Program`;
2. syntax and semantics for (classical) separation logic, fuzzy separation logic, and quantitative separation logic in `LeanFSL.SL`;
3. a framework to transform a subset of fuzzy separation logic into classical separation logic in `LeanFSL.Entailments.FSL2SL.lean` and a counter example for one naïve transformation in `LeanFSL.Entailments.FSL2SLCounter.lean`;
4. some initial, but unfinished work on a syntax for quantitative separation logic with recursively-defined predicates in `LeanFSL.Entailments.QSLSystem.lean`;
5. a framework to reason about concurrent and probabilistic programs using fuzzy separation logic in `LeanFSL.CFSL`; and
6. two examples for the use of CFSL in `LeanFSL.Examples`.

The main focus of this repository is about concurrent fuzzy separation logic, which is a logic to reason about programs that support concurrency, probabilistic branching and heap-manipulation.

## How to use

### Concurrent Fuzzy Separation Logic
To use the CFSL framework, we suggest using `safeTuple` as defined in `LeanFSL.CFSL.SafeTuple.lean`. To reason about these safe tuples, we suggest using the proof rules presented in `LeanFSL.CFSL.SafeTuple.lean` and not touch any of the other proof rules. If required, one may add new proof rules in the style of the other recommended proof rules.

The examples in `LeanFSL.Examples` show how to use this framework.

### Reasoning about Fuzzy Separation Logic
We suggest using the theorems from `LeanFSL.SL.FuzzyProofrules.lean` and `LeanFSL.SL.FuzzySubstSimp.lean` when possible and add proof rules when required.

### FSL to SL
If the fsl fragment is only mapping to 0 or 1, we suggest using conservativity theorems as presented in `LeanFSL.SL.Conservativity.lean`. Only if you cannot reduce your formula into one without any fuzzy or quantitative operations, you may use the theorems in presented in `LeanFSL.Entailments.FSL2SL.lean`.

### Other content
We currently suggest not using other contents of this repository, as it is sufficiently fleshed out yet.

## Code Conventions

### Naming
* Definitions are written in camlCase with the first letter non-capitalized
* Types are written in CamlCase with the first letter capitalized
* Theorems and Lemmas are written in underscore_non-capitalized_style
* Namespaces are aligned with mathlib when possible and like types elsewhere
* Sections are written non-capitalized without separation (but should now have multiple words)

### Proofs
The proofs currently do not follow a certain code conventions are written in best-effort style instead.