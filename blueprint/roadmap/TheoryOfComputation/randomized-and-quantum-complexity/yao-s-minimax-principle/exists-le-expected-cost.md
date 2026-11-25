# Yao's principle, lower-bound form

Let $A$ and $I$ be finite sets of deterministic algorithms and inputs, and let $C(a, x) \in \mathbb{R}$
be the cost of algorithm $a$ on input $x$. Let $c \in \mathbb{R}$. If a probability distribution $D$ on
$I$ satisfies $c \le \sum_{x \in I} D(x)\, C(a, x)$ for every $a \in A$, then every probability
distribution $R$ on $A$ (a randomized algorithm) has expected cost at least $c$ on some input: there
is $x \in I$ with $c \le \sum_{a \in A} R(a)\, C(a, x)$.

Arora and Barak: "one proves that every deterministic algorithm incurs high cost, say $C$, on this
distribution. By Yao's Lemma, it follows that the randomized complexity then is at least $C$".

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08,
  Section 11.6.
