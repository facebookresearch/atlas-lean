# Mazor–Pass: gap versions of time-bounded Kolmogorov complexity are not NP-hard under Levin reductions if iO exists

Under subexponentially secure iO, subexponentially secure one-way functions and injective PRGs, Gap$_p$MK$^t$P$[s_0,s_1]$ with $s_1$ a fixed polynomial in $\log t$ and $s_0$ is not NP-hard under Levin reductions; with DDH or LWE the gap shrinks to a factor $2+\alpha$.

For polynomials $t,p$, the promise problem Gap$_p$MK$^t$P$[s_0,s_1]$ has yes instances the strings $x$ with $\mathrm{K}^{t}(x)\le s_0(|x|)$ and no instances those with $\mathrm{K}^{p(t)}(x)>s_1(|x|)$, where $\mathrm{K}^{t}(x)$ is the length of a shortest program printing $x$ within $t(|x|)$ steps on a fixed universal machine.

1. Assume subexponentially secure iO, subexponentially secure one-way functions and injective PRGs exist. Then there is a polynomial $q$ such that for every $t\in\mathrm{poly}$, all efficiently computable $s_0,s_1$ with $s_1(n)>q(\log t(n),s_0(n))$, and every large enough polynomial $p$, Gap$_p$MK$^t$P$[s_0,s_1]$ is not NP-hard under Levin reductions; the same holds for randomized Levin reductions with $\epsilon$-error, $0\le\epsilon\le 1/30$.
2. Assume subexponentially secure iO and subexponentially secure one-way functions, and subexponential DDH or LWE. Then for every constant $\alpha>0$, every large enough polynomial $p$ and every efficiently computable $s_0$, Gap$_p$MK$^t$P$[s_0(n),(2+\alpha)s_0(n)]$ is not NP-hard under randomized Levin reductions with $\epsilon$-error.

## Expansion

The proof follows the GapMCSP argument with indistinguishability-secure randomized encodings for Turing machines in place of circuit obfuscation: the forward witness, a short program $P$ printing $f(\phi)$, is replaced by an encoding of $P$ whose length is bounded by the encoding overhead $q$, so it is a valid no-side witness of length at most $s_1$, and encodings of two programs with the same output and running time are indistinguishable. Randomized encodings with polynomial overhead follow from one-way functions, subexponentially secure iO and injective PRGs (Lin–Pass–Seth–Telang, Koppula–Lewko–Waters); with rerandomizable encryption from DDH or LWE, the overhead becomes $2(|M|+|x|)+\mathrm{poly}(\lambda,\log T)$, giving the factor $2+\alpha$ gap. The time slack $p(t)$ on the no side absorbs the decoding time.

## Depends on

- [Levin reductions (witness-preserving many-one reductions)](levin-reductions.md)
- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)
- [Indistinguishability and virtual black-box obfuscation](../../../../ComputerScience/cryptography/program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Proof depends on

- [Mazor–Pass: GapMCSP is not NP-hard under Levin reductions if iO exists](gapmcsp-not-levin-np-hard-in-obfustopia.md)

## Sources

- Noam Mazor and Rafael Pass, "Gap MCSP is not (Levin) NP-complete in Obfustopia", *39th Computational Complexity Conference (CCC 2024)*, LIPIcs, 2024, https://doi.org/10.4230/LIPIcs.CCC.2024.36; numbering from ECCC TR24-053, Revision 2, https://eccc.weizmann.ac.il/report/2024/053/revision/2/ (Theorems 1.3 and 1.4, Definition 4.1, Theorems 4.2 and 4.3, Corollary 4.4).
