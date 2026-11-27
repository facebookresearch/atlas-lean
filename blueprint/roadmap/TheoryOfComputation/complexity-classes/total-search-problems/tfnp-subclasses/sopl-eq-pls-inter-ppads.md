# Göös et al.: SOPL = PLS ∩ PPADS and EOPL = PLS ∩ PPAD

$\mathsf{SOPL}=\mathsf{PLS}\cap\mathsf{PPADS}$ and $\mathsf{EOPL}=\mathsf{PLS}\cap\mathsf{PPAD}$.

## Proof sketch

$\mathsf{SOPL}\subseteq\mathsf{PLS}\cap\mathsf{PPADS}$ is direct. For the converse, $\mathsf{PLS}\cap\mathsf{PPADS}$ has the complete problem 'solve a sink-of-DAG (local search) instance or an injective pigeonhole (inj-PHP) instance', and Lemma 3 of Göös et al. reduces it to SINK-OF-POTENTIAL-LINE on a grid: each node of the local-search instance is replaced by many copies, so that predecessors become computable, and the merging of several incoming paths into one node is hidden inside a path-pigeonhole gadget built from the inj-PHP instance (Lemma 2), so that every sink of the resulting potential line yields a local optimum or an inj-PHP solution. Together with $\mathsf{EOPL}=\mathsf{SOPL}\cap\mathsf{PPAD}$ and $\mathsf{PPAD}\subseteq\mathsf{PPADS}$ this gives the second equality.

## Depends on

- [End-of-Potential-Line and the classes EOPL and SOPL](end-of-potential-line.md)
- [The class PLS of polynomial local search problems](../the-class-pls-of-polynomial-local-search.md)

## Proof depends on

- [EOPL = SOPL ∩ PPAD](eopl-eq-sopl-inter-ppad.md)
- [Inclusions among the TFNP subclasses](tfnp-subclass-inclusions.md)

## Sources

- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Further Collapses in TFNP", 37th Computational Complexity Conference (CCC 2022), arXiv:2202.07761, 2022; SIAM Journal on Computing 53(3), 2024, Theorems 1 and 2 and Lemmas 2–4.
