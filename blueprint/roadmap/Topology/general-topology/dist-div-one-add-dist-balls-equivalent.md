# Bounded metric $d/(1+d)$ is equivalent to $d$

Let $(X,d)$ be a metric space and define

\[
\delta(x,y):=\frac{d(x,y)}{1+d(x,y)}, \qquad x,y\in X.
\]
Prove that $d$ and $\delta$ are equivalent metrics on $X$.

Lean variant: the source statement asserts only that `d`-balls and `δ`-balls are mutually nested,
which omits the claim that `δ` is a metric; the metric axioms of `δ` are added as a first conjunct.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Inequalities in real analysis), problem `ma_proofbench_l1_65`, with the change above.
