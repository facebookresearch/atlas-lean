# Ilango–Loff–Oliveira: Multi-output MCSP is NP-hard under randomized reductions

Every NP language reduces to Multi-output MCSP by a polynomial-time randomized many-one reduction with one-sided error (yes-instances always map to yes-instances; no-instances map to no-instances with probability at least $2/3$), over De Morgan bases with or without constants. Consequently Multi-output MCSP in BPP (resp. coRP) implies $\mathrm{NP} \subseteq \mathrm{BPP}$ (resp. coRP).

## Proof sketch

Reduce from gap Set Cover: each element of the universe becomes an output whose truth table is the OR of "window" functions of the sets containing it, built from random seed tables so that a small cover yields a circuit computing all windows once and sharing them. In no-instances, a union bound over all small circuits shows that with high probability none computes all outputs, since computing them would reveal a small cover.

## Depends on

- [Multi-output MCSP](multi-output-mcsp.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [The class RP](../../complexity-classes/time-and-space-complexity-classes/rp.md)

## Proof depends on

- [Lund–Yannakakis–Feige: Set Cover is NP-hard to approximate within every constant](../../pcp-and-inapproximability/approximation-hardness-of-classical-problems/set-cover-hardness-of-approximation.md)

## Sources

- R. Ilango, B. Loff and I. C. Oliveira, "NP-Hardness of Circuit Minimization for Multi-Output Functions", Computational Complexity Conference (CCC) 2020.
