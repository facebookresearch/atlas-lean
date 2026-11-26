# Sotiraki–Zampetakis–Zirdelis: BLICHFELDT and constrained SIS are PPP-complete

BLICHFELDT and cSIS are PPP-complete; cSIS is the first PPP-complete problem whose input contains no circuit or Turing machine, answering a question of Papadimitriou. Its variant weak-cSIS (no vector $b$, constraint $Gx\equiv0\pmod q$, and $m>(n+d)\ell$, so that a collision always exists) is PWPP-complete. Consequently the family $\mathcal H_{\mathrm{cSIS}}$ keyed by pairs $(A,G)$ with $G$ binary invertible, mapping a binary $x$ to the binary decomposition of $Au\bmod q$ for the binary $u$ extending $x$ with $Gu\equiv0\pmod q$, is a natural hash family that is universal in the worst case: no efficient algorithm finds collisions in every member of the family unless worst-case collision-resistant hash functions fail to exist (the corresponding worst-case assumption is $\mathsf{FP}\ne\mathsf{PWPP}$), and it is a natural candidate collision-resistant family that is universal in an average-case sense. In particular, $n$-SVP and $n^{2.5}$-CVP are Cook-reducible to BLICHFELDT, and $\tilde O(n)$-SIVP reduces to weak-cSIS and so lies in $\mathsf{PWPP}$.

## Proof sketch

BLICHFELDT in PPP: reduce each $s\in S$ modulo the fundamental parallelepiped $B[0,1)^n$, which has exactly $\det\mathcal L$ integer points, index those points via a bijection with a box $[L_1]\times\dots\times[L_n]$ (from a triangular form of $B$), and feed the map to COLLISION; a preimage of $0$ is a lattice point of $S$ and a collision gives a lattice difference. Hardness: from a COLLISION circuit $C$, take $S=\{(x,C(x))\}\subseteq\{0,1\}^{2n}$ and the lattice of vectors whose last $n$ coordinates are even, so lattice differences in $S$ are collisions. For cSIS, binary invertibility of $G$ lets one efficiently index binary solutions of $Gx\equiv b$, so membership follows from the same pigeonhole map; for hardness, the circuit of a BLICHFELDT-type instance is replaced by the purely algebraic constraint $Gx\equiv b$, BLICHFELDT serving as the intermediate intuition.

## Depends on

- [BLICHFELDT and constrained SIS: lattice-flavoured pigeonhole search problems](blichfeldt-and-constrained-sis.md)

## Sources

- Katerina Sotiraki, Manolis Zampetakis and Giorgos Zirdelis, "PPP-Completeness with Connections to Cryptography", FOCS (2018), arXiv:1808.06407.
