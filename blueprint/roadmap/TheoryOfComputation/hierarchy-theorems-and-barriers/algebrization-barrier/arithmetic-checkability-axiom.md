# Arithmetic checkability axiom

The arithmetic checkability axiom says that every $\mathsf{NP}$ language has a verifier given by an efficiently computable low-degree integer polynomial. Oracles consistent with it model arithmetization-based, algebrizing proof techniques.

A polynomial family is a sequence $f_n:\mathbb{Z}^n\to\mathbb{Z}$ of $n$-variate integer polynomials of total degree $n^{O(1)}$; it is polynomial-time computable if $F(n,y_1,\dots,y_n)=f_n(y_1,\dots,y_n)$ is in $\mathsf{FP}$.

- $\mathsf{ALG}\text{-}\mathsf{PF}$ is the class of languages $L$ for which there are a polynomial-time computable polynomial family $\{f_n\}$ and a polynomially bounded polynomial-time computable $m=m(n)$ with $x\in L$ iff some $y\in\{0,1\}^m$ has $f_{n+m}(x,y)\ne 0$.
- $\mathsf{ALG}\text{-}\mathsf{PF}^*$ is the class of $L$ with such $m$ and $\{f_n\}$ and a polynomial-time computable $g_n:\{0,1\}^n\to\{0,1\}^m$ such that $f_{n+m}(x,g_n(x))=1$ if $x\in L$, $f_{n+m}(x,g_n(x))=0$ if $x\notin L$, and $f(x,y)=0$ for every $y\ne g_n(x)$.

The weak arithmetic checkability axiom $\mathrm{ACT}$ is the statement $\mathsf{NP}=\mathsf{ALG}\text{-}\mathsf{PF}$, and the strong axiom $\mathrm{ACT}^*$ is $\mathsf{P}=\mathsf{ALG}\text{-}\mathsf{PF}^*$. An oracle $A$ is consistent with $\mathrm{ACT}$ if $\mathsf{NP}^A=\mathsf{ALG}\text{-}\mathsf{PF}^A$, and with $\mathrm{ACT}^*$ if $\mathsf{P}^A=\mathsf{ALG}\text{-}\mathsf{PF}^{*A}$. A set $A$ is self-algebrizing if some polynomial family $\tilde A\in\mathsf{P}^A$ extends $A$ under projection.

Basic facts:

1. For every oracle $A$ and every polynomial extension $\tilde A$, $\mathsf{P}^A\subseteq\mathsf{ALG}\text{-}\mathsf{PF}^{*\tilde A}$ and $\mathsf{NP}^A\subseteq\mathsf{ALG}\text{-}\mathsf{PF}^{\tilde A}$; every self-algebrizing set is consistent with $\mathrm{ACT}$ and $\mathrm{ACT}^*$.
2. For every language $L$ there is a self-algebrizing $A$ with $A\in\mathsf{PSPACE}^L$ and $L\in\mathsf{P}^A$, so consistent oracles are arbitrarily powerful.
3. For every $O$ consistent with $\mathrm{ACT}$, $\mathsf{PSPACE}^O=\mathsf{IP}^O$ and $\mathsf{MA}\text{-}\mathsf{EXP}^O\not\subset\mathsf{P}^O/\mathrm{poly}$; for every $O^*$ consistent with $\mathrm{ACT}^*$ and every $k$, $\mathsf{PP}^{O^*}\not\subset\mathrm{SIZE}^{O^*}(n^k)$, $\text{promise-}\mathsf{MA}^{O^*}\not\subset\mathrm{SIZE}^{O^*}(n^k)$ and $\mathsf{NEXP}^{O^*}[\mathrm{poly}]\subseteq\mathsf{MIP}^{O^*}$.

## Expansion

Fact 1 writes the tableau of a deterministic oracle computation as the unique proof: local tableau conditions become decision-tree polynomials, and each oracle answer $b_i$ is checked by $1-(b_i-\tilde A(0,q_i))^2$. Fact 2 is Fortnow's construction, which adds to $A$ the signs and bits of the multilinear extension of each earlier slice, so that $A$ is downward self-reducible by a polynomial-space reduction. Fact 3 runs the standard sum-check protocol on the squared verifier polynomial supplied by the axiom. The source also notes that every oracle consistent with the local checkability axiom $\mathsf{NP}=\mathsf{PF}\text{-}\mathsf{CHK}[\mathrm{poly},\log]$ is consistent with $\mathrm{ACT}$.

## Depends on

- [Multilinear extension of a Boolean function](multilinear-ext.md)
- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [NP relative to an oracle](../../complexity-classes/time-and-space-complexity-classes/npwith-oracle.md)
- [Polynomial time with an oracle](../../complexity-classes/time-and-space-complexity-classes/pwith-oracle.md)

## Proof depends on

None.

## Sources

- Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "An Axiomatic Approach to Algebrization", *Proceedings of the 41st ACM Symposium on Theory of Computing (STOC 2009)*, 2009, https://doi.org/10.1145/1536414.1536509 (Definitions 2.1 and 2.2, Theorems 2.3, 2.4, 3.1 and 3.2, Section 2).
