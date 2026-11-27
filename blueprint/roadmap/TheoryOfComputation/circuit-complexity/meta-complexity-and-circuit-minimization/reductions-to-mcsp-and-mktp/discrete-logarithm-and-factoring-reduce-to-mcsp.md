# Discrete logarithm and factoring reduce to MCSP

Discrete logarithm over prime fields is solvable in bounded-error randomized polynomial time with an oracle for the KT-random strings, hence with an MCSP oracle. Polynomial-time MCSP would also factor Blum integers well on average in subexponential time.

The *discrete logarithm problem* takes a prime $p$, an element $g$ and an element $z$ of $\mathbb{Z}_p^*$, and asks for an $i$ with $g^i\equiv z \pmod p$, or reports that $z$ is not in the orbit of $g$.

**Theorem (Allender–Buhrman–Koucký–van Melkebeek–Ronneburger).** The discrete logarithm problem is solvable in $\mathrm{BPP}^{R_{\mathrm{KT}}}$, and therefore in $\mathrm{BPP}^{\mathrm{MCSP}}$.

**Theorem (Kabanets–Cai).** If $\mathrm{MCSP}\in\mathrm{P}$, then for every $\varepsilon>0$ there is an algorithm running in time $2^{n^{\varepsilon}}$ that factors Blum integers (products of two primes congruent to $3 \bmod 4$) well on average.

## Expansion

For discrete logarithm, apply the inversion theorem for dense KT-random oracles to $f((p,g),x)=g^x \bmod p$: with the oracle, a randomized machine recovers some discrete logarithm of $g^x$ for a $1/q(n)$ fraction of $x$. Random self-reducibility handles worst-case inputs: run the inverter on $z g^v$ for many random $v$; a success $g^u=zg^v$ gives $i=u-v$, and if every trial fails, $z$ is reported outside the orbit of $g$, which is correct with high probability. For factoring, an MCSP algorithm gives a natural property useful against polynomial-size circuits, which breaks the pseudorandom generator based on factoring Blum integers.

## Depends on

- [KT complexity and the minimum KT problem MKTP](kt-complexity-and-mktp.md)
- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Proof depends on

- [Dense KT-random oracles invert polynomial-time functions](kt-random-oracles-invert-polynomial-time-functions.md)
- [Natural property](../../../hierarchy-theorems-and-barriers/natural-proofs-barrier/natural-property.md)

## Sources

- Eric Allender, Harry Buhrman, Michal Koucký, Dieter van Melkebeek, Detlef Ronneburger, "Power from Random Strings", *SIAM Journal on Computing* 35(6), 2006, https://doi.org/10.1137/050628994 (Theorem 15 and Corollary 16, numbering of the ECCC TR02-028 revision 1 edition).
- Valentine Kabanets, Jin-Yi Cai, "Circuit Minimization Problem", *Proceedings of the 32nd Annual ACM Symposium on Theory of Computing (STOC)*, 2000, https://doi.org/10.1145/335305.335314 (Theorem 2 and Corollary 3 of the full version read).
