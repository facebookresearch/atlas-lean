# Emptiness for deterministic checking stack automata with two counters is undecidable

No algorithm decides, given a one-way deterministic checking stack automaton with two reversal-bounded counters, whether it
accepts some word, although membership for such automata is decidable.

**Theorem.** The emptiness problem for $\mathrm{DCSACM}(2)$, in the sense of
[checking stack automata with reversal-bounded counters](checking-stack-automata-with-reversal-bounded.md), is undecidable.

Emptiness remains undecidable for the no-read/no-counter restriction of $\mathrm{DCSACM}(2)$ (the machine may enter the stack
and use the counters only after reaching the right input end-marker), even over letter-bounded languages. With one counter,
emptiness is decidable under the no-read/no-decrease restriction, while decidability of emptiness for unrestricted
$\mathrm{DCSACM}(1)$ is equivalent to an open problem (emptiness for two-way nondeterministic finite automata with one
reversal-bounded counter).

## Depends on

- [Checking stack automata with reversal-bounded counters](checking-stack-automata-with-reversal-bounded.md)

## Proof depends on

- [Membership for nondeterministic checking stack automata with two counters is undecidable](membership-for-nondeterministic-checking-stack.md)

## Expansion

For any complete class of machines given by store types, decidability of membership for the nondeterministic machines is
equivalent to decidability of emptiness for the deterministic machines. The undecidability of membership for
$\mathrm{NCSACM}(2)$ therefore transfers. Directly, a deterministic machine copies its one-way input onto the checking stack and
then simulates a two-way deterministic machine with two reversal-bounded counters on it, so its language is empty iff that
machine's language is.

## Sources

- O. H. Ibarra, I. McQuillan, "Variations of checking stack automata: obtaining unexpected decidability properties", *Theoretical Computer Science* 738:1–12, 2018, doi:[10.1016/j.tcs.2018.04.024](https://doi.org/10.1016/j.tcs.2018.04.024). Numbering of the version read, arXiv:1705.09732v2: Corollary 10 (emptiness), Proposition 2 (equivalent decidability properties), Corollary 17 (the no-read/no-counter restriction), Corollary 14 and Proposition 12 (one counter).
