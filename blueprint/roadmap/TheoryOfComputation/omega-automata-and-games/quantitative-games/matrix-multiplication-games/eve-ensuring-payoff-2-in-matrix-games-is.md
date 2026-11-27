# Whether the payoff Eve can ensure is below 2 in non-negative matrix multiplication games is undecidable

For matrix multiplication games with finite sets of non-negative integer matrices, it is undecidable whether the payoff that Eve can ensure stays below $2$.

**Theorem.** It is undecidable, given finite sets $\mathcal{A}, \mathcal{E}$ of non-negative matrices with integer entries, whether the maximal payoff that Eve can ensure in the [matrix multiplication game](matrix-multiplication-games.md) on $(\mathcal{A}, \mathcal{E})$ is less than $2$.

The games of the reduction are not claimed to be determined; the proof yields, from a two-counter machine $M$, non-negative integer games in which Adam can ensure payoff $< 2$ if $M$ halts and Eve can ensure payoff $\ge 2$ otherwise.

## Depends on

- [Matrix multiplication games](matrix-multiplication-games.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction follows the integer case: Eve simulates a two-counter machine and Adam can detect a cheat and reset the product. With non-negative matrices the punishment cannot cancel the product, so the simulation is weaker (Lemma 4 of the source): if the machine halts then Adam has a strategy keeping the payoff below $2$ against every strategy of Eve, and otherwise Eve has a strategy ensuring payoff at least $2$ against every strategy of Adam. Deciding whether Eve's guaranteed payoff is below $2$ would therefore decide the halting problem for two-counter machines.

## Sources

- E. Asarin, J. Cervelle, A. Degorre, C. Dima, F. Horn and V. Kozyakin, "Entropy Games and Matrix Multiplication Games", *33rd Symposium on Theoretical Aspects of Computer Science (STACS 2016)*, Leibniz International Proceedings in Informatics 47, 2016, Article 11, doi:[10.4230/LIPIcs.STACS.2016.11](https://doi.org/10.4230/LIPIcs.STACS.2016.11); numbering of arXiv:1506.04885v3: Theorem 6 with Lemma 4 (simulation of two-counter machines by non-negative integer matrices) in Section 3.
