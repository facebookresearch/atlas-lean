# Decidability of halting passes to fewer states

Let $T$ be a formal theory such that, for
every $m$ and every Busy Beaver machine $M$ with $m$ working states, if $T$ proves the halting
sentence of the embedding of $M$ into $m + 1$ states then $T$ proves the halting sentence of $M$,
and if $T$ proves the non-halting sentence of the embedding of $M$ into $m + 1$ states then $T$
proves the non-halting sentence of $M$. Then for every $n$, if $T$ decides halting for machines
with $n + 1$ working states, it decides halting for machines with $n$ working states.

The transport hypotheses are where a real theory would rewrite a proof about the embedded machine
into a proof about the original machine; they are stated explicitly because provability of one
sentence code does not formally imply provability of another.
