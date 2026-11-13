# Proof-checker presentation of a ZFC-like theory

A ZFC-like presentation consists of a
formal theory $T$, given by a provability predicate on sentence codes in $\mathbb{N}$, together
with a Boolean proof checker $\mathrm{check}(p, s)$ on pairs of natural numbers, such that the
following hold. A sentence code $s$ is provable in $T$ if and only if $\mathrm{check}(p, s)$ is true
for some $p \in \mathbb{N}$. $T$ is sound for halting: for every machine $M$, if $T$ proves the
halting sentence of $M$ then $M$ halts on the blank tape, and if $T$ proves the non-halting
sentence of $M$ then $M$ does not halt. For every machine $M$, if $M$ has halted within $t$ steps
for some $t$, then $T$ proves the halting sentence of $M$. Write $S(n)$ for the Busy Beaver shift
function, the largest halting time of a halting machine with $n$ working states, and call the
bound sentence for $n$ and $B$ the sentence code saying that every halting machine with $n$
working states halts within $B$ steps. For every $n \le 5$, $T$ proves the bound sentence for $n$
and $S(n)$. Whenever $T$ proves the bound sentence for $n$ and $B$, every halting machine with $n$
working states halts within $B$ steps. Whenever $T$ proves the bound sentence for $n$ and $B$ and a
machine $M$ with $n$ working states has not halted within $B$ steps, $T$ proves the non-halting
sentence of $M$.

No concrete syntax or proof checker for ZFC is given, and no presentation of ZFC is constructed;
the intended instance is ZFC with its standard proof checker. The state counts for
consistency-search machines in the literature depend on specific checker implementations and are
not asserted for arbitrary presentations.
