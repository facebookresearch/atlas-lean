# Adically complete modules

Let $R$ be a commutative ring, $I \subseteq R$ an ideal and $M$ an $R$-module. The module $M$ is
$I$-adically complete if it is Hausdorff, $\bigcap_{n \ge 0} I^n M = 0$, and precomplete: every
sequence $(x_n)_{n \ge 0}$ in $M$ with $x_m \equiv x_n \pmod{I^m M}$ for all $m \le n$ has an $x \in
M$ with $x_n \equiv x \pmod{I^n M}$ for all $n$. These two conditions say that the map $M \to
\varprojlim_n M / I^n M$ is injective and surjective. The ring $R$ is $I$-adically complete if it is
so as a module over itself.

## Sources

- The Stacks Project, Definition 10.96.2, <https://stacks.math.columbia.edu/tag/0317>.
