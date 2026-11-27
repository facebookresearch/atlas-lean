# Mazor–Pass: GapMCSP is not NP-hard under Levin reductions if iO exists

If indistinguishability obfuscation and subexponentially secure one-way functions exist, then for some polynomial $p$, every GapMCSP$[s_0,s_1]$ with $s_1>p(s_0)$ is not NP-hard under (randomized) Levin reductions.

For $s_0,s_1:\mathbb{N}\to\mathbb{N}$, GapMCSP$[s_0,s_1]$ has yes instances the truth tables $x\in\{0,1\}^{n}$, $n=2^{k}$, computed by a circuit of size at most $s_0(n)$ and no instances those computed by no circuit of size $s_1(n)$; thresholds are functions of the truth-table length $n$. Its relations are $R_Y=\{(x,C):|C|\le s_0(n),\ C\text{ computes }x\}$ and $R_N=\{(x,C):|C|\le s_1(n),\ C\text{ computes }x\}$.

**Theorem.** Let $0\le\epsilon\le 1/30$ and let $p:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$. Assume there exist an indistinguishability obfuscator with overhead $p$ (obfuscations of $C$ at security parameter $\lambda$ have size at most $p(|C|,\lambda)$) and subexponentially secure one-way functions. Then for every constant $\alpha>0$ and all efficiently computable $s_0,s_1$ with $s_1(n)>p(s_0(n),s_0(n)^{\alpha})$, GapMCSP$[s_0,s_1]$ is not NP-hard under randomized Levin reductions with $\epsilon$-error.

Since every obfuscator has polynomial overhead: if iO and subexponentially secure one-way functions exist, there is a polynomial $p$ such that GapMCSP$[s_0(n),s_1(n)]$ is not NP-hard under Levin reductions whenever $s_1(n)>p(s_0(n))$. For honest reductions, iO together with $\mathsf{NP}\not\subseteq\mathsf{ioBPP}$ suffices, provided also $s_0(n)>n^{\epsilon'}$ for some $\epsilon'>0$.

## Expansion

Use a target collision-resistant hash $T:\{0,1\}^{n}\to\{0,1\}^{n-\omega(\log n)}$ (from one-way functions, Rompel) and the formulas $\phi_{T(x)}[x']=1\iff T(x')=T(x)$ for random $x$; finding a second satisfying assignment is a collision. Given a Levin reduction $(f,g,h)$ from SAT, the algorithm $A(\phi,v)=h(\phi,\mathrm{iO}(g(\phi,v)))$ obfuscates the forward witness circuit. Its size is below $s_1(|f(\phi)|)$, so it is a valid no-side witness and $h$ returns a satisfying assignment. For two satisfying $v\neq v'$ the circuits $g(\phi,v)$ and $g(\phi,v')$ compute the same truth table $f(\phi)$, so iO makes the two outputs indistinguishable, and $A$ outputs some $v'\neq v$ with probability at least $1/4$, contradicting target collision resistance. Subexponential security only rules out reductions whose outputs are so short that $s_0(|f(\phi)|)<n^{\delta}$, where brute force would invert $T$.

## Depends on

- [Levin reductions (witness-preserving many-one reductions)](levin-reductions.md)
- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../../circuit-complexity/minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Indistinguishability and virtual black-box obfuscation](../../../../ComputerScience/cryptography/program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Proof depends on

- [Rompel: one-way functions yield universal one-way hash functions](../../inaccessible-entropy-and-universal-one-way-hashing/rompel-one-way-functions-yield-uowhfs.md)
- [One-way function families](../../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Sources

- Noam Mazor and Rafael Pass, "Gap MCSP is not (Levin) NP-complete in Obfustopia", *39th Computational Complexity Conference (CCC 2024)*, LIPIcs, 2024, https://doi.org/10.4230/LIPIcs.CCC.2024.36; numbering from ECCC TR24-053, Revision 2, https://eccc.weizmann.ac.il/report/2024/053/revision/2/ (Theorems 1.1, 1.2, 3.2 and 3.7, Definitions 2.8 and 3.1, Claims 3.3 and 3.4, Lemma 3.6).
