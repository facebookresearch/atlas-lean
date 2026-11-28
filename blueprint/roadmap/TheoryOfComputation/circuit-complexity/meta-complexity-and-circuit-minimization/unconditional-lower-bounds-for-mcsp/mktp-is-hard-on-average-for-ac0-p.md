# MKTP is hard on average for AC0[p]

For every prime $p$, no polynomial-size $\mathrm{AC}^0[p]$ circuit family solves MKTP on average, even with zero-sided error on all but an $\varepsilon$ fraction of inputs, for any constant $\varepsilon\in(0,1)$. This strengthens earlier worst-case $\mathrm{AC}^0[p]$ lower bounds for MKTP.

**Theorem (Hirahara–Santhanam).** There is a threshold function $s(n)$ such that $\mathrm{MKTP}[s]$ is not in $\mathrm{AC}^0[p]$ on average with error $\varepsilon$, for every prime $p$ and every constant $\varepsilon\in(0,1)$. Here an $\mathrm{AC}^0[p]$ circuit computes a language on average with error $\varepsilon$ if, on each input length, it outputs the correct answer or "?" on every input and outputs "?" on at most an $\varepsilon$ fraction of inputs under the uniform distribution. In the case $p\ne2$ the proof takes $s(n)=n-\sqrt{n}$.

## Expansion

The proof breaks the Fefferman–Shaltiel–Umans–Viola generator $G(x_1,\dots,x_k)=x_1\cdots x_k\cdot\mathrm{PARITY}(x_1)\cdots\mathrm{PARITY}(x_k)$ (for odd $p$). Its outputs are implicitly computable, so $\mathrm{KT}(G(x))\le nk+n\,\mathrm{polylog}(n)$, which for $k=n^3$ is below the threshold, while uniform strings exceed it except with probability $o(1)$. Replacing "?" by $1$, an average-case circuit for $\mathrm{MKTP}[s]$ accepts every output of $G$ and at most an $\varepsilon+o(1)$ fraction of uniform strings, so it distinguishes $G$. By resamplability of parity, any such distinguisher gives an $\mathrm{AC}^0$ circuit with oracle gates computing parity exactly, which an $\mathrm{AC}^0[p]$ circuit for odd $p$ cannot do by Razborov–Smolensky. For $p=2$ the generator is replaced by one based on the connectivity matrix determinant problem, whose outputs satisfy $\mathrm{KT}\le nk+n^{O(1)}$ and whose distinguishers give $\mathrm{AC}^0[2]$ oracle circuits for majority, contradicting Razborov's lower bound.


Expanding this node to full proof readiness requires planned proof-prerequisite pages for:

- Fefferman–Shaltiel–Umans–Viola resamplability lemmas (Hirahara–Santhanam Lemmas 32 and 36)

## Depends on

- [KT complexity and the minimum KT problem MKTP](../reductions-to-mcsp-and-mktp/kt-complexity-and-mktp.md)
- [AC0(m): constant-depth circuits with MOD gates](../../../complexity-classes/time-and-space-complexity-classes/ac0-mod.md)

## Proof depends on

- [Razborov: majority is not in AC0(2)](../../razborov-majority-not-in-ac0-mod-two.md)
- [Smolensky's theorem: MOD_q is not in AC0(p)](../../constant-depth-circuit-lower-bounds/smolensky-s-theorem-mod-q-is-not-in-ac0-p.md)

## Sources

- Shuichi Hirahara, Rahul Santhanam, "On the Average-Case Complexity of MCSP and Its Variants", *Computational Complexity Conference (CCC)*, 2017, https://doi.org/10.4230/LIPIcs.CCC.2017.7 (Theorem 30, Definition 31, Lemma 32, Claims 33 and 34, Fact 35, Lemma 36).
