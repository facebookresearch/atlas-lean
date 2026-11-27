# Razborov–Smolensky polynomial approximation of AC0[p]

Let $p$ be a prime and $C$ a circuit of depth $d$ and size $s$ with unbounded fan-in AND, OR, NOT and $\mathrm{MOD}_p$ gates on $n$ inputs. For every $\ell \ge 1$ there is a polynomial $P \in \mathbb{F}_p[x_1, \dots, x_n]$ of degree at most $((p-1)\ell)^d$ that agrees with $C$ on all but at most $s \cdot 2^{n - \ell}$ inputs in $\{0,1\}^n$. Taking $\ell = \Theta(\log s)$ gives degree $O((\log s)^d)$ and agreement on at least a $3/4$ fraction of inputs.

## Depends on

- [The class $\mathsf{ACC}^0$](../../complexity-classes/time-and-space-complexity-classes/acc0.md)

## Sources

- R. Smolensky, "Algebraic methods in the theory of lower bounds for Boolean circuit complexity", *Proceedings of the 19th ACM STOC*, 1987
- R. Williams, *CS294 lecture notes: AC0 with parity gates and the polynomial method*, 2018, <https://people.csail.mit.edu/rrw/cs294-2018/ac0-parity2.txt>
