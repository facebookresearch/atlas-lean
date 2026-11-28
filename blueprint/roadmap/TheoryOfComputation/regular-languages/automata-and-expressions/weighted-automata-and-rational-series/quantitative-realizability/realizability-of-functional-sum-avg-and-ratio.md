# Realizability of functional Sum-, Avg- and Ratio-automata is undecidable

No algorithm decides whether the controller wins the quantitative realizability game defined by a functional weighted
automaton with sum, average or ratio measure.

**Theorem.** Let $V \in \{\mathrm{Sum}, \mathrm{Avg}, \mathrm{Ratio}\}$. The quantitative language realizability problem for
functional $V$-automata, in the sense of
[functional weighted automata and quantitative language realizability](functional-weighted-automata-and-quantitative.md),
is undecidable.

For deterministic $V$-automata the problem is decidable. The discounted-sum case is left open by the source.

## Depends on

- [Functional weighted automata and quantitative language realizability](functional-weighted-automata-and-quantitative.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Reduce the halting problem of deterministic two-counter machines. The controller's letters are the machine's instructions,
so a play spells a claimed run; the environment's letters are a neutral move and *cheat* signals, one for each kind of
error (a zero test passed on a nonzero counter, a decrement of a zero counter, a structural error in the sequence of
instructions). For each cheat signal a gadget of the automaton counts the relevant counter with weights so that a faithful
run receives a positive value and a run with the signalled error a negative one; the gadgets are arranged so that the
automaton stays functional. The controller wins iff it can spell an accepting run of the machine and stop, that is, iff the
machine halts. An Avg-automaton becomes a Ratio-automaton by replacing each weight $w$ by $(w + K, 1)$ and the threshold $\nu$ by $\nu + K$, where $K$ makes every weight nonnegative (the gadgets use the weight $-1$, so $K = 1$); this shift raises every Avg value by exactly $K$ and keeps Ratio weights natural, as the definition requires. Besides the linked results, a good expansion links a page for the correctness and functionality of the cheat gadgets (Section 5.1 of the source).

## Sources

- E. Filiot, R. Gentilini, J.-F. Raskin, "Quantitative languages defined by functional automata", *Logical Methods in Computer Science* 11(3), article 14, 2015, doi:[10.2168/LMCS-11(3:14)2015](https://doi.org/10.2168/LMCS-11(3:14)2015). Numbering of the version read, arXiv:1111.0862v4: Theorem 5.1 (undecidability), Theorem 5.2 (deterministic automata) and the encoding in Section 5.1.
