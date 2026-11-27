# NP ⊊ NEXP, P ⊊ E ⊊ EXP and PSPACE ⊊ EXPSPACE

On binary words: $\mathsf{P}\subsetneq\mathsf{E}\subsetneq\mathsf{EXP}$, $\mathsf{NP}\subsetneq\mathsf{NEXP}$, and $\mathsf{PSPACE}\subsetneq\mathsf{EXPSPACE}$. Moreover $\mathsf{E}$ is not closed under polynomial-time many-one reductions, hence $\mathsf{E}\ne\mathsf{NP}$ and $\mathsf{E}\ne\mathsf{PSPACE}$.

## Proof sketch

The general hierarchy theorems separate the classes: the deterministic time hierarchy for time-constructible $f,g$ with $f\log f=o(g)$ (Arora–Barak Theorem 3.1) gives $\mathsf{P}\subseteq\mathsf{DTIME}(2^{n})\subsetneq\mathsf{DTIME}(2^{2n})\subseteq\mathsf{E}$ and $\mathsf{E}\subseteq\mathsf{DTIME}(2^{n^{3/2}})\subsetneq\mathsf{DTIME}(2^{n^{2}})\subseteq\mathsf{EXP}$; the nondeterministic time hierarchy for $f(n+1)=o(g(n))$ (Theorem 3.3) gives $\mathsf{NP}\subseteq\mathsf{NTIME}(2^{n})\subsetneq\mathsf{NTIME}(2^{n^{2}})\subseteq\mathsf{NEXP}$; the space hierarchy gives $\mathsf{PSPACE}\subsetneq\mathsf{EXPSPACE}$ in the same way. The linked hierarchy pages are the special cases $n$ versus $n^2$ of the first two theorems. For non-closure, pick $L\in\mathsf{DTIME}(2^{n^2})\setminus\mathsf{E}$ and pad it to quadratic length: $L'=\{x10^{|x|^2} : x\in L\}$: then $L'\in\mathsf{E}$ and $x\mapsto x10^{|x|^2}$ reduces $L$ to $L'$ in polynomial time, so closure would put $L$ in $\mathsf{E}$. Since $\mathsf{NP}$ and $\mathsf{PSPACE}$ are closed under these reductions, neither equals $\mathsf{E}$.

## Depends on

- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [The class E](../../complexity-classes/time-and-space-complexity-classes/e.md)
- [The class EXP](../../complexity-classes/time-and-space-complexity-classes/exp.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The complexity class NEXP](../../complexity-classes/time-and-space-complexity-classes/nexp.md)
- [Polynomial space for decision problems](../../complexity-classes/time-and-space-complexity-classes/pspace.md)
- [The class EXPSPACE](../../complexity-classes/time-and-space-complexity-classes/expspace.md)

## Proof depends on

- [Deterministic time hierarchy: quadratic versus linear time](../time-hierarchy-theorem/time-hierarchy.md)
- [Nondeterministic time hierarchy](../nondet-time-hierarchy.md)
- [Space hierarchy theorem for space-constructible bounds](../space-hierarchy-theorem/space-hierarchy-theorem-for-space-constructible.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009, Chapter 3 (Theorems 3.1–3.3 in the 2007 web draft).
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
- Ronald V. Book, "Comparing Complexity Classes", Journal of Computer and System Sciences 9(2), 213–229, 1974.
