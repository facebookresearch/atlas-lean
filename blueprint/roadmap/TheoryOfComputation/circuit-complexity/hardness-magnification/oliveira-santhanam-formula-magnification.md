# Oliveira–Santhanam: formula lower bounds for approximate MCSP above N polylog N give NP ⊄ Formula[poly]

Let $s_2$ and $1/\delta$ be polynomially bounded. If for every $c$ some $2^n$-bit slice of $(1, 1-\delta)\text{-}\mathrm{MCSP}[s_1, s_2]$ has no separating De Morgan formula of leaf size $(2^n + 1)\, c\,(n + 1)^c$, then NP (for the succinct MCSP encoding) is not contained in the class of polynomial-size formulas. Under the stronger hypothesis of formula lower bounds $N^{1 + \varepsilon}$ at arbitrarily large $n$, some NP language has formula size not $O(2^{m^\gamma})$ for some $\gamma > 0$; with subexponentially bounded $s_2$ and $1/\delta$ and lower bounds $2^{n + n/d}$ or $N^{1+\varepsilon}$ the conclusion $\mathrm{NP} \not\subseteq \mathrm{Formula}[\mathrm{poly}]$ again follows.

## Proof sketch

Two-stage magnification (Lemma 16 of the source): if Succinct MCSP had small formulas, then approximate MCSP is solved by sampling $\mathrm{poly}(s_2/\delta)$ random positions of the truth table (hard-wired as a formula over the samples) and applying the small formula for Succinct MCSP to the sampled instance, giving formulas of leaf size $N\,\mathrm{polylog}(N)$; the parameter regimes follow by scaling the instance size.

## Depends on

- [Approximate MCSP](approximate-mcsp.md)
- [Succinct MCSP](../minimum-circuit-size-problem/succinct-mcsp.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Sources

- I. C. Oliveira and R. Santhanam, "Hardness Magnification for Natural Problems", FOCS 2018.
