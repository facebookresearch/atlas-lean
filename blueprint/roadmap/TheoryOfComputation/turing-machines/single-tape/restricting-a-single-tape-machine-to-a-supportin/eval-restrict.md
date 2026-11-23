# The restricted machine evaluates like the original

Let $M$ be a single-tape Turing machine
with tape alphabet $\Gamma$ and states $\Lambda$, and let $S \subseteq \Lambda$ be a set of states
that supports $M$: it contains the default state and is closed under the transitions of $M$. If the
default state of the restriction of $M$ to $S$ is the default state of $M$, then for every input
list $l$ over $\Gamma$ the evaluation of the restricted machine on $l$ equals that of $M$: either
both fail to halt, or both halt with the same output.
