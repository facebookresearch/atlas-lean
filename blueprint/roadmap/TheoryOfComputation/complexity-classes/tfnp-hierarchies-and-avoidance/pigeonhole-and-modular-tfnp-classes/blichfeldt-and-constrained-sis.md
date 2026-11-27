# BLICHFELDT and constrained SIS: lattice-flavoured pigeonhole search problems

For a full-rank basis $B\in\mathbb Z^{n\times n}$ let $\mathcal L=B\mathbb Z^n$. Blichfeldt's theorem: if $S\subseteq\mathbb R^n$ is measurable with $\mathrm{vol}(S)>\det\mathcal L$, there are $x\ne y\in S$ with $x-y\in\mathcal L$. A **value function** representation of a finite $S\subseteq\mathbb Z^n$ is a pair $(s,V_S)$ with $V_S$ a circuit mapping indices $z\in[s]$ to elements of $S$.

**BLICHFELDT.** Input: $B$ and $(s,V_S)$. Output: if $s<\det\mathcal L$, the zero vector; otherwise one of: an index $z$ with $V_S(z)\notin S$ or $z\ne w$ with $V_S(z)=V_S(w)$; a vector $x\in S\cap\mathcal L$; or $x\ne y\in S$ with $x-y\in\mathcal L$.

**Binary invertible matrices.** For $q\le2^\ell$, with gadget vector $\gamma=(1,2,\dots,2^{\ell-1})$, a matrix $G=[(I_d\otimes\gamma^{\top}+U)\mid V]\in\mathbb Z_q^{d\times(d\ell+k)}$ with $U$ supported strictly above a diagonal band and $V$ arbitrary has the property that for every $b$ a binary $r$ with $Gr\equiv b$ is computable by back-substitution.

**cSIS (constrained SIS).** Input: $A\in\mathbb Z_q^{n\times m}$, a binary invertible $G\in\mathbb Z_q^{d\times m}$ and $b\in\mathbb Z_q^d$ with $m\ge(n+d)\ell$. Output: $x\in\{0,1\}^m$ with $Ax\equiv0$ and $Gx\equiv b\pmod q$, or $x\ne y\in\{0,1\}^m$ with $A(x-y)\equiv0$ and $Gx\equiv Gy\equiv b\pmod q$. No circuit appears in the input.

## Depends on

- [Search problems: FNP, FP and TFNP](../../total-search-problems/search-problems-fnp-fp-and-tfnp.md)

## Sources

- Katerina Sotiraki, Manolis Zampetakis and Giorgos Zirdelis, "PPP-Completeness with Connections to Cryptography", FOCS (2018), arXiv:1808.06407.
