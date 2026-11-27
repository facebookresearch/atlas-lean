# Padding: upward translation of class collapses

Let $f(n)>n$ be time-constructible and let $t_1(n)\ge n$. If $\mathsf{DTIME}(t_1(n))\subseteq\mathsf{DTIME}(t_2(n))$ then $\mathsf{DTIME}(t_1(f(n)))\subseteq\mathsf{DTIME}(t_2(f(n))+O(f(n)))$; analogous statements hold for nondeterministic time and deterministic space. In particular $\mathsf{P}=\mathsf{NP}\Rightarrow\mathsf{EXP}=\mathsf{NEXP}$ and $\mathsf{NP}\subseteq\mathsf{P}\Rightarrow\mathsf{E}=\mathsf{NE}$.

## Proof sketch

For $L\in\mathsf{DTIME}(t_1(f(n)))$, the padded language $L'=\{x01^{f(|x|)-|x|-1} : x\in L\}$ has inputs of length exactly $m=f(|x|)$; checking the padding uses the time-constructibility of $f$ and costs $O(m)$, which $t_1(m)\ge m$ absorbs, so $L'\in\mathsf{DTIME}(t_1(m))$. By hypothesis $L'\in\mathsf{DTIME}(t_2(m))$, and $L$ is decided by writing the padding in time $O(f(n))$ and running that machine (the translation lemma; Fortnow–Santhanam, Lemma 5).

## Depends on

- [Deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)
- [Nondeterministic time classes](../../complexity-classes/time-and-space-complexity-classes/ntime.md)
- [Deterministic space classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dspace.md)
- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The class EXP](../../complexity-classes/time-and-space-complexity-classes/exp.md)
- [The complexity class NEXP](../../complexity-classes/time-and-space-complexity-classes/nexp.md)
- [The class E](../../complexity-classes/time-and-space-complexity-classes/e.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009, Chapter 2 ($\mathsf{P}=\mathsf{NP}\Rightarrow\mathsf{EXP}=\mathsf{NEXP}$ by padding; Theorem 2.25 in the 2007 web draft).
- Lance Fortnow and Rahul Santhanam, "Recent Work on Hierarchies for Semantic Classes", ACM SIGACT News 37(3), 2006, Lemma 5.
- Christos H. Papadimitriou, "Computational Complexity", Addison-Wesley, 1994.
