# NEXP ⊆ NP^{R_C}

Nondeterministic exponential time reduces to the Kolmogorov-random strings in nondeterministic polynomial time: $\mathrm{NEXP}\subseteq\mathrm{NP}^{R_C}$. Access to random strings gives a provable exponential speed-up, in contrast to the weakness of nonadaptive reductions to them.

$$
\mathrm{NEXP}\subseteq\mathrm{NP}^{R_C}.
$$

This extends $\mathrm{PSPACE}\subseteq\mathrm{P}^{R_K}$ of Allender, Buhrman, Koucký, van Melkebeek and Ronneburger, who also prove $\mathrm{EXP}=\mathrm{NP}^{R_{Kt}}$ for the set $R_{Kt}$ of strings $x$ with Levin complexity $\mathrm{Kt}(x)\ge|x|/2$. Allender, Buhrman, Friedman and Loff note that $\mathrm{PSPACE}\subseteq\mathrm{P}^{R}$ and $\mathrm{NEXP}\subseteq\mathrm{NP}^{R}$ hold for both plain and prefix-free complexity and for every choice of universal machine.

## Expansion

It suffices to show $\mathrm{NEXP}\subseteq\mathrm{MA}^{R_C}$, since $\mathrm{MA}^{R_C}=\mathrm{NP}^{R_C}$ by the derandomization results of Allender et al. Every NEXP language has a two-prover interactive proof (Babai, Fortnow and Lund). The optimal prover strategies are computable, hence in $\mathrm{P}^{R_C}/\mathrm{poly}$ by Allender et al. Merlin sends oracle circuits $C_1,C_2$ computing the two provers' strategies relative to $R_C$, and Arthur simulates the verifier against them.

## Depends on

- [Sets of Kolmogorov-random strings R_C, R_K and R_{K^t}](kolmogorov-random-strings.md)
- [The complexity class NEXP](../../../complexity-classes/time-and-space-complexity-classes/nexp.md)
- [NP relative to an oracle](../../../complexity-classes/time-and-space-complexity-classes/npwith-oracle.md)

## Proof depends on

None.

## Sources

- Eric Allender, Harry Buhrman and Michal Koucký, "What Can Be Efficiently Reduced to the Kolmogorov-Random Strings?", *Annals of Pure and Applied Logic* 138(1–3), 2006, [doi:10.1016/j.apal.2005.06.003](https://doi.org/10.1016/j.apal.2005.06.003) (Theorem 6; numbering of the ECCC TR04-044 version).
- Eric Allender, Harry Buhrman, Michal Koucký, Dieter van Melkebeek and Detlef Ronneburger, "Power from Random Strings", *SIAM Journal on Computing* 35(6), 2006, [doi:10.1137/050628994](https://doi.org/10.1137/050628994) (Theorems 11 and 13; numbering of ECCC TR02-028, revision 1).
- Eric Allender, Harry Buhrman, Luke Friedman and Bruno Loff, "Reductions to the set of random strings: The resource-bounded case", *Logical Methods in Computer Science* 10(3:5), 2014, DOI 10.2168/LMCS-10(3:5)2014, [arXiv:1406.7658v2](https://arxiv.org/abs/1406.7658v2) (Section 1).
