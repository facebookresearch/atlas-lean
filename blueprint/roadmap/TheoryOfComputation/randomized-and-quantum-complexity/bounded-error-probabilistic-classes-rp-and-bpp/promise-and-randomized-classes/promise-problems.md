# Promise problems and promise classes

A **promise problem** is a pair $\Pi=(\Pi_{\mathrm{yes}},\Pi_{\mathrm{no}})$ of disjoint sets of instances. An algorithm solves $\Pi$ if it accepts every yes-instance and rejects every no-instance; its behaviour outside $\Pi_{\mathrm{yes}}\cup\Pi_{\mathrm{no}}$ is unconstrained. For $\mathcal{C}\in\{\mathsf{P},\mathsf{NP},\mathsf{coNP}\}$, $\mathrm{promise}\text{-}\mathcal{C}$ consists of the promise problems $\Pi$ having a separating language $L\in\mathcal{C}$ with $\Pi_{\mathrm{yes}}\subseteq L$ and $L\cap\Pi_{\mathrm{no}}=\emptyset$. The semantic classes are defined directly by machines whose error bounds are required only on promised instances: $\Pi\in\mathrm{promise}\text{-}\mathsf{BPP}$ if some probabilistic polynomial-time machine accepts every yes-instance with probability at least $2/3$ and every no-instance with probability at most $1/3$; $\mathrm{promise}\text{-}\mathsf{RP}$ requires probability at least $1/2$ on yes-instances and $0$ on no-instances, and $\mathrm{promise}\text{-}\mathsf{coRP}$ probability $1$ on yes-instances and at most $1/2$ on no-instances. Such a machine need not have bounded error off the promise, so the machine itself need not decide a language in $\mathsf{BPP}$, $\mathsf{RP}$ or $\mathsf{coRP}$.

## Depends on

- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [The class RP](../../../complexity-classes/time-and-space-complexity-classes/rp.md)
- [Polynomial-time reduction between promise problems](../../local-hamiltonian-problem/promise-reduces.md)

## Sources

- Oded Goldreich, "On Promise Problems: A Survey", in Theoretical Computer Science: Essays in Memory of Shimon Even, Lecture Notes in Computer Science 3895, 254–290, 2006.
- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
