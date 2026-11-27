# A large formal complexity measure is large on a quarter of all functions

Let $\mu$ be a formal complexity measure on the Boolean functions of $n$ variables. If $\mu(f)\ge c$ for some function $f$, then at least one quarter of all $2^{2^n}$ Boolean functions $g$ satisfy $\mu(g)\ge c/4$. (Hence formal complexity measures always define large properties, the reason formula-size lower bounds via such measures are natural.)

## Proof sketch

For any $g$ put $h=f\oplus g$; then $f=(g\wedge\neg h)\vee(\neg g\wedge h)$, so $c\le\mu(g)+\mu(\neg g)+\mu(h)+\mu(\neg h)$ and one of these four functions has measure at least $c/4$. When $g$ is uniform, each of $g,\neg g,h,\neg h$ is uniform, so $1\le 4\Pr_u[\mu(u)\ge c/4]$ for a uniform function $u$.

## Depends on

- [Formal complexity measures](formal-complexity-measures.md)

## Sources

- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Lemma 22.2.
- Alexander A. Razborov, Steven Rudich, "Natural Proofs", Journal of Computer and System Sciences 55(1), 24–35, 1997.
