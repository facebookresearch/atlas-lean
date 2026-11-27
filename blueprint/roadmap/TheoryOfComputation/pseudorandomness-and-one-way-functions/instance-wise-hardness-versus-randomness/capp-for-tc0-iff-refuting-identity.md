# Chen–Tell–Williams: CAPP for TC0 in polynomial time iff Identity has an FP-refuter against TC0∘XOR

Let $\mathrm{Identity}(x)=x$. Threshold gates have polynomially bounded weights. The following are equivalent:

1. There is a deterministic polynomial-time algorithm solving CAPP (distinguishing acceptance probability at least $2/3$ from at most $1/3$) for $\mathrm{TC}^0$ circuits.
2. For some $\varepsilon>0$ there is an FP-refuter for $\mathrm{Identity}$ against probabilistic $\mathrm{TC}^0\circ\oplus$ circuits with $O(n^{1+\varepsilon})$ wires and $n^{\varepsilon}$ gates in the bottom XOR layer.

For $\varepsilon<1$ such circuits unconditionally fail to compute $\mathrm{Identity}$, since they have public-coin two-party communication complexity $O(n^{\varepsilon})$ while computing $\mathrm{Identity}$ requires exchanging $n/2$ bits; only a deterministic witness of the failure is missing.

## Proof sketch

The Chen–Tell targeted hitting-set generator is scaled down to $\mathrm{TC}^0$: its layered-polynomial representation and reconstruction are implemented by constant-depth threshold circuits whose dependence on the input passes through few parities. An input on which the reconstruction circuit fails to print $x$ itself is then exactly a refutation of $\mathrm{Identity}$, and conversely a $\mathrm{CAPP}$ algorithm derandomizes the trivial random refuter.

## Depends on

- [Refuters for a function against a class of probabilistic algorithms](refuter-for-a-function.md)

## Proof depends on

- [Chen–Tell–Williams: refuting low-space streaming algorithms is equivalent to prBPP = prP](refuting-streaming-algorithms-iff-prbpp-eq-prp.md)
- [Chen–Tell instance-wise reconstruction: a targeted HSG from a shallow logspace-uniform circuit](instance-wise-reconstruction-targeted-hsg.md)

## Sources

- Lijie Chen, Roei Tell and Ryan Williams, "Derandomization vs Refutation: A Unified Framework for Characterizing Derandomization", FOCS (2023), ECCC TR23-105.
