# Small bounded-error probability SBP

$L\in\mathsf{SBP}$ if there are a polynomial-time predicate $V$, a polynomial $p$ and a polynomial-time computable threshold $k(n)$ such that $x\in L$ implies $\Pr_{r\in\{0,1\}^{p(n)}}[V(x,r)=1]\ge 2^{-k(n)}$ and $x\notin L$ implies $\Pr_r[V(x,r)=1]\le 2^{-k(n)-1}$. The gap can be amplified uniformly, and $\mathsf{MA}\subseteq\mathsf{SBP}\subseteq\mathsf{AM}$.

## Depends on

- [The class MA (Merlin–Arthur)](../../complexity-classes/time-and-space-complexity-classes/ma.md)
- [The class $\mathsf{AM}$ (Arthur–Merlin)](../../complexity-classes/time-and-space-complexity-classes/am.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
