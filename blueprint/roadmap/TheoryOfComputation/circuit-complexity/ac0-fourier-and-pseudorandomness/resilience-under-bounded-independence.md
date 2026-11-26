# Resilient monotone AC0 functions stay resilient under bounded independence

Let $f$ be computed by a monotone circuit of the unbounded fan-in basis of constant depth and polynomial size. If $f$ is nearly balanced and *$(q,\varepsilon)$-resilient* under the uniform distribution (every coalition $Q$ of at most $q$ coordinates determines the output with probability at most $\varepsilon$ over the other coordinates), then the same holds, up to an additive error $2^{-p}$, under every $t$-wise independent distribution with $t\ge\mathrm{poly}(p)$ (polylogarithmic in $n$ for $p=O(\log n)$). For example the Tribes function $\mathrm{Tribes}_{w,s}$, an OR of $s$ ANDs of $w$ inputs, keeps its near balance and resilience under $(64p)^{157}$-wise independence when $2s+8\le 2^p$ and $w<2^p$.

## Proof sketch

For monotone $f$, a coalition $Q$ fails to be outvoted at $x$ exactly when $f$ is $1$ with $Q$ set to all ones and $0$ with $Q$ set to all zeros; this event is computed by a constant-depth circuit made of two copies of the circuit for $f$, so Braverman's theorem transfers its probability from the uniform distribution to the $t$-wise independent one.

## Depends on

- [k-wise independent and almost k-wise independent distributions](k-wise-independent-distributions.md)
- [Unbounded fan-in signature](../unbounded-fan-in-circuits/ac-signature.md)

## Proof depends on

- [Braverman: polylogarithmic independence fools AC0](braverman-polylog-independence-fools-ac0.md)

## Sources

- Eshan Chattopadhyay, David Zuckerman, "Explicit Two-Source Extractors and Resilient Functions", Annals of Mathematics, 2019.
- Mark Braverman, "Polylogarithmic Independence Fools AC^0 Circuits", Journal of the ACM, 2010.
