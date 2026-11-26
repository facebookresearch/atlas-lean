# Parallel repetition theorem (Raz, Holenstein)

For every two-prover one-round game $G$ with answer sets satisfying $|A||B| \ge 2$ and value $\mathrm{val}(G) \le 1 - \varepsilon$, and every $n \ge 1$ (Holenstein 2009, Theorem 2.5, stated there with $1 - \mathrm{val}(G)$ in place of $\varepsilon$),

$$\mathrm{val}(G^n) \le \Big(1 - \frac{\varepsilon^3}{6000}\Big)^{n / \log_2(|A||B|)}.$$

In particular, if $\mathrm{val}(G) < 1$ then $\mathrm{val}(G^n)$ decays exponentially in $n$ with a rate depending only on $\varepsilon$ and the answer-set sizes.

## Proof sketch

Build the set $C$ of coordinates greedily: as long as $\Pr[W_C]$ is not already small, the embedding lemma shows that some free coordinate is won with probability at most $1 - \varepsilon/2$ conditioned on $W_C$ (otherwise the players could win $G$ with probability above $\mathrm{val}(G)$). Adding it multiplies $\Pr[W_C]$ by at most $1 - \varepsilon/2$; a recursion on $|C|$ yields the bound.

## Depends on

- [Parallel repetition of a two-prover game](parallel-repetition-of-a-game.md)

## Proof depends on

- [Holenstein's embedding lemma for conditioned repetitions](holenstein-embedding-lemma.md)

## Sources

- R. Raz, "A Parallel Repetition Theorem", SIAM Journal on Computing 27(3), 1998.
- T. Holenstein, "Parallel Repetition: Simplifications and the No-Signaling Case", Theory of Computing 5, 2009.
