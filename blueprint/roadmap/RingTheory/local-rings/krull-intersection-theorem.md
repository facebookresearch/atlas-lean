# Krull's intersection theorem for finitely generated modules over a Noetherian local ring

Let $R$ be a commutative Noetherian local ring, $I \ne R$ an ideal and $M$ a finitely generated
$R$-module. Then $\bigcap_{i \ge 0} I^i M = 0$.

It follows from the [Artin–Rees lemma](artin-rees-lemma.md) and Nakayama's lemma: the intersection
$N$ satisfies $N = I^n M \cap N = I^{n-k}(I^k M \cap N) \subseteq IN$ for large $n$, so $N = 0$.
Applied to $M / E$ for a submodule $E \subseteq M$, it gives $\bigcap_{i \ge 0} (E + I^i M) = E$.

## Sources

- The Stacks Project, Lemma 10.51.4 (Krull's intersection theorem),
  <https://stacks.math.columbia.edu/tag/00IP>.
