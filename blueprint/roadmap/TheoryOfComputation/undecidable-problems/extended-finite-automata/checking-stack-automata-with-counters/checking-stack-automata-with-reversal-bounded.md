# Checking stack automata with reversal-bounded counters

A checking stack automaton has a stack that it may only push onto while writing, and may then read from the inside in
read-only mode; adding reversal-bounded counters gives the classes DCSACM and NCSACM.

A *checking stack* over a stack alphabet $\Gamma_0$ starts empty (between a bottom and a top marker) and is used in two
phases. In the *writing phase* the machine may push a symbol of $\Gamma_0$ or leave the stack unchanged, but never pop; at
some point it enters the *reading phase*, in which the stack head moves down, up or stays inside the stack in two-way
read-only mode, and the stack can never be changed again. A *counter* stores a natural number that can be incremented,
decremented and tested for zero; it is *$l$-reversal-bounded* if it alternates between non-decreasing and
non-increasing mode at most $l$ times. Following the source, the bound is part of the machine: $l$ is given with $M$, and a computation can accept only if each counter respects it (the store type's instruction language), so reversal-boundedness is a syntactic restriction checked along the computation rather than a semantic promise about all computations.

A *one-way* machine reads its input $\triangleright w \triangleleft$ (between end-markers) from left to right; a transition
depends on the state, the input symbol, the symbol under the stack head and the zero status of each counter, and it updates
the state, the stores and the input head. It accepts $w$ if some computation from the initial configuration reaches an
accepting state; it is *deterministic* if the transition relation is a partial function.

- $\mathrm{NCSACM}(k)$ (resp. $\mathrm{DCSACM}(k)$) is the class of one-way nondeterministic (resp. deterministic) machines
  with one checking stack and $k$ counters, each $l$-reversal-bounded for some $l$.

- $\mathrm{NCSA}$ and $\mathrm{DCSA}$ are the checking stack automata without counters; $2\mathrm{DCM}(k)$ denotes two-way
  deterministic finite automata with $k$ reversal-bounded counters.

The *membership problem* for a class asks, given a machine $M$ and a word $w$, whether $M$ accepts $w$; the *emptiness
problem* asks, given $M$, whether $L(M) = \emptyset$.

## Depends on

None.

## Proof depends on

None.

## Expansion

For any complete class of machines defined by store types, the source shows that emptiness for the deterministic one-way
machines, emptiness and membership for the nondeterministic one-way machines, acceptance of the empty word by
nondeterministic one-way machines, and membership for two-way multi-head nondeterministic machines are all equivalently
decidable, because a machine can encode a fixed input word in its states. For checking stack automata with reversal-bounded
counters the deterministic membership problem is nevertheless decidable.

## Sources

- O. H. Ibarra, I. McQuillan, "Variations of checking stack automata: obtaining unexpected decidability properties", *Theoretical Computer Science* 738:1–12, 2018, doi:[10.1016/j.tcs.2018.04.024](https://doi.org/10.1016/j.tcs.2018.04.024). Numbering of the version read, arXiv:1705.09732v2: Section 2 (store types, checking stacks, machines and the classes DCSACM(k) and NCSACM(k)) and Lemma 1 and Proposition 2 of Section 3.
