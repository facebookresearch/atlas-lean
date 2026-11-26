# Padding: upward translation of class collapses

Let $f(n)\ge n$ be time-constructible. If $\mathsf{DTIME}(t_1(n))\subseteq\mathsf{DTIME}(t_2(n))$ then $\mathsf{DTIME}(t_1(f(n)))\subseteq\mathsf{DTIME}(t_2(f(n))+O(f(n)))$; analogous statements hold for nondeterministic time and deterministic space. In particular $\mathsf{P}=\mathsf{NP}\Rightarrow\mathsf{EXP}=\mathsf{NEXP}$ and $\mathsf{NP}\subseteq\mathsf{P}\Rightarrow\mathsf{E}=\mathsf{NE}$.

## Proof sketch

For $L$ in the larger-bound class, the padded language $L'=\{x\#1^{f(|x|)-|x|}\}$ lies in the smaller-bound class relative to its own length; apply the hypothesis to $L'$ and strip the padding.

## Depends on

- [Deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)
- [Nondeterministic time classes](../../complexity-classes/time-and-space-complexity-classes/ntime.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- Christos H. Papadimitriou, "Computational Complexity", Addison-Wesley, 1994.
