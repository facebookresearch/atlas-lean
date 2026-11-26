# Blum: any two complexity measures are recursively related

Let $\Phi$ and $\Psi$ be Blum complexity measures for the same acceptable numbering $(\varphi_c)$ of partial computable functions. There is a total computable $r:\mathbb{N}^2\to\mathbb{N}$ such that for every program $c$ and almost every $n$ (indeed all $n\ge c$) with $\varphi_c(n)$ defined, $\Psi_c(n)\le r(n,\Phi_c(n))$ and $\Phi_c(n)\le r(n,\Psi_c(n))$.

## Proof sketch

Define $r(n,m)=\max\{\Psi_c(n),\Phi_c(n) : c\le n,\ \Phi_c(n)=m\text{ or }\Psi_c(n)=m\}$; the Blum axioms make the predicate '$\Phi_c(n)=m$' decidable, so the maximum ranges over a finite decidable set.

## Depends on

- [Blum complexity measure](../blum-measure.md)

## Sources

- Manuel Blum, "A Machine-Independent Theory of the Complexity of Recursive Functions", Journal of the ACM 14(2), 1967.
- Piergiorgio Odifreddi, "Classical Recursion Theory, Volume II", North-Holland, 1999.
