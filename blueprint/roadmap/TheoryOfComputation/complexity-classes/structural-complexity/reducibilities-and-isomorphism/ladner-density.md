# Ladner's density theorem for polynomial-time degrees

Let $A<^{p}_{m}B$ (i.e. $A\le^{p}_{m}B$ and $B\not\le^{p}_{m}A$) be languages over $\{0,1\}$ with $B$ decidable and $B\notin\mathsf{P}$. Then there is a decidable $C$ with $A<^{p}_{m}C<^{p}_{m}B$; if $A,B\in\mathsf{NP}$, then $C$ can be taken in $\mathsf{NP}$. In particular, if $\mathsf{P}\ne\mathsf{NP}$, below every $\mathsf{NP}$-complete language there is an $\mathsf{NP}$-intermediate language, and the polynomial-time many-one degrees of decidable sets outside $\mathsf{P}$ are dense.

## Proof sketch

Apply Schöning's uniform diagonalization to the decidable classes $\mathcal{C}_1=\{L : L\le^p_m A\}$ and $\mathcal{C}_2=\{L : B\le^p_m A\oplus L\}$, which are recursively presentable and closed under finite variations, with $B\notin\mathcal{C}_1$ and $\emptyset\notin\mathcal{C}_2$. It yields $G\in\mathsf{P}$ such that $D=B\cap G$ lies in neither class. Then $C=A\oplus D$ satisfies $A\le^p_m C\le^p_m B$, $C\not\le^p_m A$ (else $D\le^p_m A$) and $B\not\le^p_m C$; if $A,B\in\mathsf{NP}$ then $C\in\mathsf{NP}$. (If $A$ is $\emptyset$ or $\{0,1\}^*$, any $C\in\mathsf{P}$ other than $\emptyset$ and $\{0,1\}^*$ works.)

## Depends on

- [Transitivity of polynomial-time many-one reductions](../../../np-completeness/satisfiability/3-satisfiability/poly-many-one-red-trans.md)
- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Ladner's theorem: NP-intermediate languages exist](../../ladner.md)
- [Schöning's uniform diagonalization theorem](../uniform-diagonalization-and-closure-properties/uniform-diagonalization.md)
- [Recursively presentable complexity classes](recursively-presentable-classes.md)

## Sources

- Richard E. Ladner, "On the Structure of Polynomial Time Reducibility", Journal of the ACM 22(1), 1975.
- Uwe Schöning, "A Uniform Approach to Obtain Diagonal Sets in Complexity Classes", Theoretical Computer Science 18(1), 1982.
