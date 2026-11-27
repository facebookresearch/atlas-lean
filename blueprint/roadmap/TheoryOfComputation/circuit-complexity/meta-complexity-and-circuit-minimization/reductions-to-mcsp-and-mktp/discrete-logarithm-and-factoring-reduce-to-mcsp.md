# Discrete logarithm reduces to MCSP, and easy MCSP rules out strong pseudorandom generators

Discrete logarithm over prime fields is solvable in bounded-error randomized polynomial time with an oracle for the KT-random strings, hence with an MCSP oracle. If MCSP is in P/poly, no strong pseudorandom generator is computable in P/poly, so in particular the generator based on factoring Blum integers can be broken.

The *discrete logarithm problem* takes a prime $p$, an element $g$ and an element $z$ of $\mathbb{Z}_p^*$, and asks for an $i$ with $g^i\equiv z \pmod p$, or reports that $z$ is not in the orbit of $g$.

**Theorem (Allender–Buhrman–Koucký–van Melkebeek–Ronneburger).** The discrete logarithm problem is solvable in $\mathrm{BPP}^{R_{\mathrm{KT}}}$, and therefore in $\mathrm{BPP}^{\mathrm{MCSP}}$.

The *hardness* $H(G_k)$ of a generator $G_k:\{0,1\}^k\to\{0,1\}^{2k}$ is the least $s$ such that some circuit $C$ of size at most $s$ satisfies $|\Pr_{x\in\{0,1\}^k}[C(G_k(x))=1]-\Pr_{y\in\{0,1\}^{2k}}[C(y)=1]|>1/s$, and the generator is *strong* if $H(G_k)>2^{k^{\Omega(1)}}$.

**Theorem (Kabanets–Cai).** If $\mathrm{MCSP}\in\mathrm{P/poly}$, then there is no strong pseudorandom generator in P/poly.

Kabanets and Cai draw from this the informal Corollary 3: if $\mathrm{MCSP}\in\mathrm{P}$, then for every $\varepsilon>0$ there is an algorithm running in time $2^{n^{\varepsilon}}$ that factors Blum integers (products of two primes congruent to $3 \bmod 4$) "well on the average". The precise content is the theorem above applied to the pseudorandom generator based on factoring Blum integers, whose breaking yields average-case factoring; the source does not quantify "well on the average" further.

## Expansion

For discrete logarithm, apply the inversion theorem for dense KT-random oracles to $f((p,g),x)=g^x \bmod p$: with the oracle, a randomized machine recovers some discrete logarithm of $g^x$ for a $1/q(n)$ fraction of $x$. Random self-reducibility handles worst-case inputs: run the inverter on $z g^v$ for many random $v$; a success $g^u=zg^v$ gives $i=u-v$, and if every trial fails, $z$ is reported outside the orbit of $g$, which is correct with high probability. For the second theorem, an MCSP algorithm in P/poly gives a P/poly-natural property useful against P/poly (the truth tables of high circuit complexity), and the Razborov–Rudich theorem turns such a property into a distinguisher for every generator in P/poly.

## Depends on

- [KT complexity and the minimum KT problem MKTP](kt-complexity-and-mktp.md)
- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [Polynomial time with polynomial advice](../../../complexity-classes/time-and-space-complexity-classes/ppoly.md)

## Proof depends on

- [Dense KT-random oracles invert polynomial-time functions](kt-random-oracles-invert-polynomial-time-functions.md)
- [Natural property](../../../hierarchy-theorems-and-barriers/natural-proofs-barrier/natural-property.md)
- [Razborov-Rudich: the natural proofs barrier](../../../hierarchy-theorems-and-barriers/natural-proofs-barrier/razborov-rudich-natural-proofs.md)

## Sources

- Eric Allender, Harry Buhrman, Michal Koucký, Dieter van Melkebeek, Detlef Ronneburger, "Power from Random Strings", *SIAM Journal on Computing* 35(6), 2006, https://doi.org/10.1137/050628994 (Theorem 15 and Corollary 16, numbering of the ECCC TR02-028 revision 1 edition).
- Valentine Kabanets, Jin-Yi Cai, "Circuit Minimization Problem", *Proceedings of the 32nd Annual ACM Symposium on Theory of Computing (STOC)*, 2000, https://doi.org/10.1145/335305.335314 (Section 2.1, Theorems 1 and 2, Corollary 3, numbering of the full version dated 15 November 1999, ECCC TR99-045).
