# Invariance theorem for time-bounded complexity

Let $M$ and $N$ be description methods such that $N$ *simulates* $M$: every $M$-program $p$ compiles to an $N$-program of length at most $|p| + c$ with the same output, and if $p$ halts within $t$ steps then the compiled program halts within $\tau(|p|)\, t$ steps, with $\tau$ monotone. Then $C_N(x) \le C_M(x) + c$, and $K^{t}_M(x) \le k$ implies $K^{\tau(k) t}_N(x) \le k + c$. For the universal machine and any multi-tape machine $M$ the overhead is polynomial: there are a polynomial $p$ and a constant $c$ with $K^{p(t)}_U(x) \le K^t_M(x) + c$ for all $x$ and $t$, and $Kt_U(x) \le Kt_M(x) + O(\log |x|)$.

## Proof sketch

Compose the compilation with the description; the step bound follows from the simulation overhead applied to the run of length at most $t$.

## Depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Proof depends on

- [Optimality (the invariance theorem)](../exists-k-le-of-partrec.md)

## Sources

- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
- M. Sipser, "Introduction to the Theory of Computation", 3rd ed., Cengage Learning, 2013.
