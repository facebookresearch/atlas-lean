# EG-emptiness of L/U parametric timed automata is undecidable

No algorithm decides whether some parameter valuation gives an L/U parametric timed automaton a maximal run that stays in
a given set of locations, already with four clocks and three parameters.

**Theorem.** The EG-emptiness problem is undecidable for L/U-PTAs with at least $4$ clocks and $3$ parameters: no algorithm
decides, given such an automaton $\mathcal{A}$ and a set $T$ of locations, whether the set of parameter valuations $v$ such
that some maximal run of $v(\mathcal{A})$ stays in $T$ is empty. Automata, maximal runs and EG-emptiness are as in
[parametric timed automata](parametric-timed-automata.md).

EG-emptiness is also undecidable for open bounded L/U-PTAs with at least $4$ clocks and $4$ parameters and for PTAs with at
least $4$ clocks and $2$ parameters, whereas it is decidable for closed bounded L/U-PTAs. EG-emptiness is the dual of
AF-universality.

## Depends on

- [Parametric timed automata](parametric-timed-automata.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from the halting problem of two-counter machines, with an encoding inspired by Benes, Bezdek, Larsen and
Srba, in which two clocks hold the counter values themselves and a parameter bounds them. The parameter is split into a
lower-bound parameter $a^-$ and an upper-bound parameter $a^+$, and a fresh clock that is never reset after initialization,
with the invariant that it stays below a fresh upper-bound parameter $b^+$, bounds the total duration of the execution. The
interplay of these bounds makes a maximal run that stays in the chosen locations correspond to a faithful simulation. The
decidable closed bounded case uses the monotonicity of L/U-PTAs in their lower- and upper-bound parameters.

## Sources

- É. André, D. Lime, O. H. Roux, "Reachability and liveness in parametric timed automata", *Logical Methods in Computer Science* 18(1), article 31, 2022, doi:[10.46298/lmcs-18(1:31)2022](https://doi.org/10.46298/lmcs-18(1:31)2022). Numbering of the version read, arXiv:2004.09171v4: Theorem 5.13 (L/U-PTAs), Theorem 5.11 (open bounded L/U-PTAs), Corollary 5.17 (PTAs) and Theorem 5.10 (the decidable closed bounded case).
