# Effective proof length of adaptive PCP verifiers

Fix an input $x$ and let a (possibly adaptive) PCP verifier on $x$ be given as a family $(T_\rho)_{\rho \in \{0,1\}^r}$ of decision trees over the proof positions, each of depth at most $q$. Then the set of proof positions that the verifier can ever query, over all random strings and all proofs, has at most $2^{q + r}$ elements. Consequently, without loss of generality the proofs of a $\mathrm{PCP}(r, q)$ verifier have length at most $2^{q + r}$ on each input.

## Proof sketch

A decision tree of depth at most $q$ has at most $2^q - 1$ internal nodes, each labelled by one position; taking the union over the $2^r$ random strings gives at most $2^r (2^q - 1) < 2^{q+r}$ positions.

## Depends on

- [Local test on a proof string](local-test-on-a-proof-string.md)
- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)
- [Probabilistically checkable proofs](../../complexity-classes/time-and-space-complexity-classes/pcp.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
