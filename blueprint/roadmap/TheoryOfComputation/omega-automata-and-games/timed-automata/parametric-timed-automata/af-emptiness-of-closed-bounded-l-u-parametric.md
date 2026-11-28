# AF-emptiness of closed bounded L/U parametric timed automata is undecidable

No algorithm decides whether some parameter valuation forces every maximal run of an L/U parametric timed automaton to
visit a target location, already for closed bounded L/U-PTAs with three clocks and two rational-valued parameters.

**Theorem.** The AF-emptiness problem is undecidable for closed bounded L/U-PTAs with at least $3$ clocks and $2$
rational-valued parameters: no algorithm decides, given such an automaton $\mathcal{A}$ and a set $T$ of target locations,
whether the set of parameter valuations $v$ in the bounds such that every maximal run of $v(\mathcal{A})$ visits $T$ is
empty. Automata, maximal runs and AF-emptiness are as in [parametric timed automata](parametric-timed-automata.md).

The proof of the source's Corollary 5.2 runs the same construction with both parameters bounded by $(0, 1]$, an open bounded L/U-PTA. AF-emptiness is also undecidable for bounded integer-points PTAs, for
integer-points PTAs and for bounded PTAs. This contrasts with EF-emptiness, which is decidable for L/U-PTAs.

## Depends on

- [Parametric timed automata](parametric-timed-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

In the closed bounded encoding of a two-counter machine used for EF-emptiness, the single parameter $a$ is used both as a
lower and as an upper bound. Replace it by a lower-bound parameter $a^-$ and an upper-bound parameter $a^+$: a guard
$y = 1 + a$ becomes the guard $1 + a^- \le y$ together with the invariant $y \le 1 + a^+$. An initial gadget makes the first
machine location unavoidable exactly when $a^- = a^+ > 0$, since for $a^- = 0$ a sink is reachable and otherwise some run can
be blocked by an invariant. With $a^- = a^+ > 0$ the invariants rule out infinite delays and no run blocks inside a gadget, so
the halting location is unavoidable for some valuation exactly when the machine halts; the parameters can be bounded by
$[0, 1]$.

## Sources

- É. André, D. Lime, O. H. Roux, "Reachability and liveness in parametric timed automata", *Logical Methods in Computer Science* 18(1), article 31, 2022, doi:[10.46298/lmcs-18(1:31)2022](https://doi.org/10.46298/lmcs-18(1:31)2022). Numbering of the version read, arXiv:2004.09171v4: Theorem 5.1 (closed bounded L/U-PTAs), Corollary 5.2 (open bounded L/U-PTAs) and Corollary 5.3 (integer-points and bounded PTAs).
