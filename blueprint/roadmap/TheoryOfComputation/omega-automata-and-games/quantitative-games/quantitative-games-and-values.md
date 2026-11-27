# Quantitative games and their values

A *quantitative game* is an [arena](../muller-rabin-and-streett-games/arenas-strategies-and-memory-structures.md) whose two players are called Max
(who plays Eve's part) and Min, together with a *quantitative condition* $f : \mathrm{Paths}^\omega \to \mathbb{R} \cup \{\pm\infty\}$, usually
induced by a colouring of the edges and an objective on infinite sequences of colours. A strategy $\sigma$ of Max *ensures* $x$
from $v$ if $f(\pi) \ge x$ for every play $\pi$ from $v$ consistent with $\sigma$, and dually for Min with $f(\pi) \le x$. Writing $\pi^v_{\sigma,\tau}$
for the play from $v$ consistent with $\sigma$ and $\tau$, the *value of Max* and the *value of Min* from $v$ are

$$\mathrm{val}^{\mathcal{G}}_{\mathrm{Max}}(v) = \sup_\sigma \inf_\tau f(\pi^v_{\sigma,\tau}), \qquad \mathrm{val}^{\mathcal{G}}_{\mathrm{Min}}(v) = \inf_\tau \sup_\sigma f(\pi^v_{\sigma,\tau}),$$

and always $\mathrm{val}^{\mathcal{G}}_{\mathrm{Max}}(v) \le \mathrm{val}^{\mathcal{G}}_{\mathrm{Min}}(v)$. The game is *determined* at $v$ when they are equal, and the common
number is the *value* $\mathrm{val}^{\mathcal{G}}(v)$. A strategy $\sigma$ of Max is *optimal* from $v$ if $\inf_\tau f(\pi^v_{\sigma,\tau}) = \mathrm{val}^{\mathcal{G}}_{\mathrm{Max}}(v)$, and
symmetrically for Min. A quantitative objective is *positional* if in every game with that objective, from every vertex $v$ and for every threshold $x$,
whenever Max has a strategy ensuring $x$ from $v$ she has a positional one; it is *bi-positional* if moreover the same holds for Min with the
dual meaning of ensuring. When optimal strategies are guaranteed to exist, this amounts to positional optimal strategies for Max, respectively
for both players; *uniformly* means that one strategy serves from every vertex. A threshold
$x$ turns $f$ into the qualitative condition $f_{\ge x} = \{\pi : f(\pi) \ge x\}$.

## Depends on

- [Arenas, strategies and memory structures](../muller-rabin-and-streett-games/arenas-strategies-and-memory-structures.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 1 (N. Fijalkow, "Introduction"): Section 1.9, "Quantitative games", "Values in quantitative games" (including Fact 1.9) and Definitions 1.9 and 1.10.
