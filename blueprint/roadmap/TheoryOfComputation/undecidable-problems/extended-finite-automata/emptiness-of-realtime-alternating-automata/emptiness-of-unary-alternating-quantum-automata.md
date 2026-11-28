# Emptiness of unary alternating quantum finite automata is undecidable

No algorithm decides, given a realtime alternating quantum finite automaton over a one-letter alphabet, whether it accepts some input.

**Theorem.** The emptiness problem for realtime [alternating quantum finite automata](alternating-quantum-finite-automata.md) over unary alphabets is undecidable: there is no algorithm that, given an AQFA $R$ with input alphabet $\{a\}$, decides whether $R$ accepts some word $a^m$. Instances are finite: the entries of the operation elements are algebraic numbers, each given by its minimal polynomial over $\mathbb Q$ and an isolating interval (the source states the theorem without fixing the amplitudes; its examples, as in Theorem 4.3, use rational entries).

Unary NQFAs and UQFAs recognize only regular languages, so the undecidability comes from combining the two kinds of branching.

## Depends on

- [Alternating quantum finite automata](alternating-quantum-finite-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

One-way AQFAs can simulate any Turing machine (Yakaryılmaz): after reading the input, the head rests on the right end-marker while the automaton guesses successive configurations existentially and eliminates wrong guesses with universal branches, running forever if the machine does not halt. For a Turing machine $M$, the realtime AQFA $R$ runs a number of steps of the one-way simulation of $M$ on the empty word that grows with the length of its unary input. If $M$ halts on the empty word and accepts, some (indeed infinitely many) sufficiently long inputs are accepted; otherwise none is. A decision procedure for emptiness would therefore decide whether a Turing machine accepts the empty word.

## Sources

- H. Gökalp Demirci, Mika Hirvensalo, Klaus Reinhardt, A. C. Cem Say and Abuzer Yakaryılmaz, "Alternating, private alternating, and quantum alternating realtime automata", *Logical Methods in Computer Science* 15(3), 2019, paper 22, doi:[10.23638/LMCS-15(3:22)2019](https://doi.org/10.23638/LMCS-15(3:22)2019); numbering of arXiv:1407.0334v5 ([arXiv](https://arxiv.org/abs/1407.0334v5)): Theorem 4.4 and its proof.
