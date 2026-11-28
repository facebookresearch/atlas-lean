# Membership for nondeterministic checking stack automata with two counters is undecidable

No algorithm decides, given a one-way nondeterministic checking stack automaton with two reversal-bounded counters and an
input word, whether the automaton accepts the word.

**Theorem.** The membership problem for $\mathrm{NCSACM}(2)$, in the sense of
[checking stack automata with reversal-bounded counters](checking-stack-automata-with-reversal-bounded.md), is undecidable.

The proof uses only the empty input word. By contrast, membership is decidable for deterministic checking stack automata with reversal-bounded counters, even
two-way with several input heads, and both membership and emptiness are decidable for one-way nondeterministic
reversal-bounded counter machines without a stack. The source presents $\mathrm{NCSACM}$ as the first known model whose
deterministic version has decidable membership while deterministic emptiness, nondeterministic membership and
nondeterministic emptiness are undecidable.

## Depends on

- [Checking stack automata with reversal-bounded counters](checking-stack-automata-with-reversal-bounded.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Reduce emptiness of two-way deterministic machines with two reversal-bounded counters over letter-bounded languages, which
is undecidable (Ibarra, via Hilbert's tenth problem). From such a machine $M$ construct an $\mathrm{NCSACM}(2)$ machine $M'$
that, on the empty input, guesses an input $w$ of $M$ and writes it on its checking stack, then simulates $M$ on $w$, using the
two-way read-only stack as $M$'s input tape and the two counters as $M$'s counters. Then $M'$ accepts the empty word iff
$L(M) \ne \emptyset$.

## Sources

- O. H. Ibarra, I. McQuillan, "Variations of checking stack automata: obtaining unexpected decidability properties", *Theoretical Computer Science* 738:1–12, 2018, doi:[10.1016/j.tcs.2018.04.024](https://doi.org/10.1016/j.tcs.2018.04.024). Numbering of the version read, arXiv:1705.09732v2: Proposition 9 (membership), Proposition 8 (the result of Ibarra used in the proof, restated with its citation), Proposition 7 (deterministic membership) and the summary after Corollary 10.
