# Resilient monotone AC0 functions stay resilient under bounded independence

Let $f : \{0,1\}^n \to \{0,1\}$ be computed by a monotone circuit of unbounded fan-in, depth $d$ and size $M$, and call $f$ *$(q,\varepsilon)$-resilient* under a distribution $D$ if for every coalition $Q$ of at most $q$ coordinates the probability over the remaining coordinates that $Q$ cannot fix the output is at least $1 - \varepsilon$ (equivalently, the bias under fixing $Q$ changes by at most $\varepsilon$). If $f$ has bias $|\Pr_U[f(x)=1] - 1/2| \le \delta$ and is $(q,\varepsilon)$-resilient under the uniform distribution $U$, then under every $t$-wise independent distribution $D$ with $t \ge (\log(2M) + p)^{c_d}$ (for the constant $c_d = O(d^2)$ of Braverman's theorem), $f$ has bias at most $\delta + 2^{-p}$ and is $(q, \varepsilon + 2^{-p})$-resilient. In particular, the Tribes function $\mathrm{Tribes}_{w,s}$, an OR of $s$ ANDs of $w$ inputs, keeps its bias and resilience within $2^{-p}$ under $(64p)^{157}$-wise independence when $2s+8\le 2^p$ and $w<2^p$.

## Proof sketch

For monotone $f$, a coalition $Q$ fails to be outvoted at $x$ exactly when $f$ is $1$ with $Q$ set to all ones and $0$ with $Q$ set to all zeros; this event is computed by a constant-depth circuit made of two copies of the circuit for $f$, so Braverman's theorem transfers its probability from the uniform distribution to the $t$-wise independent one.

## Depends on

- [k-wise independent and almost k-wise independent distributions](k-wise-independent-distributions.md)
- [Unbounded fan-in signature](../../unbounded-fan-in-circuits/ac-signature.md)

## Proof depends on

- [Braverman: polylogarithmic independence fools AC0](braverman-polylog-independence-fools-ac0.md)

## Sources

- Eshan Chattopadhyay, David Zuckerman, "Explicit Two-Source Extractors and Resilient Functions", Annals of Mathematics, 2019.
- Mark Braverman, "Polylogarithmic Independence Fools AC^0 Circuits", Journal of the ACM, 2010.
