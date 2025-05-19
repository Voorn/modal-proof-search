# modal-proof-search

This is the repository accompanying the TABLEAUX 2025 submission title: Forward Proof Search for Intuitionistic Multimodal K Logics

The repository contains two artefacts:

1. In the Agda subfolder, there is a partial formalisation of the first half of the paper. That is, it has the cut elimination proof for the multimodal intuitionistic sequent calculus given that: all modalities satisfy axiom K and N, and we have a general axiomatic scheme for elaborating modalities, that is axioms of the form: M X => N1 N2 N3 ... Nn X. This system needs to be decomposable: for any pair of modalities M and N there must be a set (M-N) covering all axioms M X => N R1 R2 ... Rn X. The formalisation itself has the additional restriction where the (M-N) sets can have at most one modality, as the more general case is difficult to get past Agda's termination checker. This holds for all examples.

This formalisation was checked with Agda version 2.6.3.

Special thanks to: Gan Shen for his original formalisation of cut elimination for intuitionistic logic. His repository is at: github.com/gshen42

3. In the Haskell subfolder there is a rudimentary implementation of the forward proof search algorithm. Code only uses the Haskell standard library. Run main.hs with choice of "testbag---" examples from MExample.hs as an argument to "drunner". Here "drunner" uses focussing whereas "runner" does not. The algorithm will produces a stream of derived sequents. Once saturated, it will print the full knowledge database as a tree data structure. Then it will revisit the original query, and produce all provable minimal sequents relevant to this query.
