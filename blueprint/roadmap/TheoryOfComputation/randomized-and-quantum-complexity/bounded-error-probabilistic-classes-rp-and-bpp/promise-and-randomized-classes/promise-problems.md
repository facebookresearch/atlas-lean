# Promise problems and promise classes

A **promise problem** is a pair $\Pi=(\Pi_{\mathrm{yes}},\Pi_{\mathrm{no}})$ of disjoint sets of instances. An algorithm solves $\Pi$ if it accepts every yes-instance and rejects every no-instance; its behaviour outside $\Pi_{\mathrm{yes}}\cup\Pi_{\mathrm{no}}$ is unconstrained. For a class $\mathcal{C}$ of languages, $\mathrm{promise}\text{-}\mathcal{C}$ consists of promise problems $\Pi$ having a separating language $L\in\mathcal{C}$ with $\Pi_{\mathrm{yes}}\subseteq L$ and $L\cap\Pi_{\mathrm{no}}=\emptyset$; for semantic classes such as $\mathsf{BPP},\mathsf{RP}$ the probabilistic error bounds are required only on promised instances (promise-BPP, promise-RP, promise-coRP).

## Depends on

- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [The class RP](../../../complexity-classes/time-and-space-complexity-classes/rp.md)
- [Polynomial-time reduction between promise problems](../../local-hamiltonian-problem/promise-reduces.md)

## Sources

- Oded Goldreich, "On Promise Problems: A Survey", in Theoretical Computer Science: Essays in Memory of Shimon Even, Lecture Notes in Computer Science 3895, 254–290, 2006.
- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
