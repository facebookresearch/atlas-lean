# Ladner's density theorem for polynomial-time degrees

Let $A<^{p}_{m}B$ (i.e. $A\le^{p}_{m}B$ and $B\not\le^{p}_{m}A$) be languages over $\{0,1\}$ with $B$ decidable and $B\notin\mathsf{P}$. Then there is a decidable $C$ with $A<^{p}_{m}C<^{p}_{m}B$; if $A,B\in\mathsf{NP}$, then $C$ can be taken in $\mathsf{NP}$. In particular, if $\mathsf{P}\ne\mathsf{NP}$, below every $\mathsf{NP}$-complete language there is an $\mathsf{NP}$-intermediate language, and the polynomial-time many-one degrees of decidable sets are dense.

## Proof sketch

Uniform diagonalization (Schöning): the recursively presentable classes $\{C : C\le^p_m A\}$-complement conditions are combined by a 'delayed' union $C=(B\cap G)\cup(A\cap\overline{G})$ where $G\in\mathsf{P}$ alternates between long blocks; each block waits until a new candidate reduction or decider has been refuted, which is possible because both $\{L: B\le L\}$ and $\{L: L\le A\}$ fail on finite variations of $B$ and $A$.

## Depends on

- [Transitivity of polynomial-time many-one reductions](../../np-completeness/satisfiability/3-satisfiability/poly-many-one-red-trans.md)
- [The complexity class NP](../the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Ladner's theorem: NP-intermediate languages exist](../ladner.md)
- [Recursively presentable complexity classes](recursively-presentable-classes.md)

## Sources

- Richard E. Ladner, "On the Structure of Polynomial Time Reducibility", Journal of the ACM 22(1), 1975.
- Uwe Schöning, "A Uniform Approach to Obtain Diagonal Sets in Complexity Classes", Theoretical Computer Science 18(1), 1982.
