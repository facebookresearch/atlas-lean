# LONG CHOICE is total and PPP-hard, PWPP reduces to UNARY LONG CHOICE, and multi-colour Ramsey lies in PLC

(i) LONG CHOICE is total and in TFNP, and remains total when $a_0$ is prescribed. (ii) LONG CHOICE is PPP-hard, so $\mathsf{PPP}\subseteq\mathsf{PLC}$. (iii) WEAK-PIGEON reduces to UNARY LONG CHOICE. (iv) For all $r,n$, $(r,n)$-RAMSEY (given a circuit $r$-colouring the edges of the complete graph on $r^{rn}$ vertices, each an $rn\lceil\log r\rceil$-bit string, find a monochromatic $n$-clique) reduces to BINARY LONG CHOICE, hence lies in PLC. (v) NAIVE SUNFLOWER (given a circuit describing $2^{k^3\log k}$ distinct $k$-sets, find a duplicated element or set, or a sunflower of size $k^2$) reduces to multi-colour Ramsey. Pasarkar, Papadimitriou and Yannakakis leave open whether RAMSEY or the sunflower problem is PLC-complete.

## Proof sketch

(i): by the majority argument, after choosing $a_0,\dots,a_i$ at least $2^{n-i}$ candidates remain, enough to complete a sequence of length $n+1$. (ii): given a COLLISION circuit $C$, let $P_i$ ask whether $C(x)$ lies in a sub-interval $F_i$ of the current interval $B_i$ of hole values, chosen so that the unfilled holes are split in half; any certificate forces two elements whose images are $0$ apart, a collision, or an image $0$. (iii): let $P_i(x)$ be the $(i+1)$-st bit of $C(x)$; then $a_{n-1},a_n$ agree on all $n-1$ bits. (iv): for each group of $\lceil\log r\rceil$ steps starting at index $k = \lfloor i / \lceil\log r\rceil \rfloor \lceil\log r\rceil$, the binary predicates $P_i(a_k, x)$ encode the bits of the edge colour between $a_k$ and $x$ (using $k \le i$ as allowed by BINARY LONG CHOICE), so every chosen vertex at a group boundary has a single colour to every vertex after its group (in particular to every later group-boundary vertex), and a pigeonhole argument on those group-boundary vertices yields a monochromatic $n$-clique. (v): pairwise equidistant $k$-sets under $d(A,B)=|A\triangle B|/2$ form a sunflower once there are at least $k^2-k+2$ of them (Deza), so colour pairs by distance.

## Depends on

- [LONG CHOICE and the class PLC of polynomial long choice for iterated pigeonhole arguments](long-choice-and-plc.md)
- [Jeřábek: integer factoring randomly reduces to PPA and to WEAK-PIGEON, and modular square roots lie in PPA](factoring-reduces-to-ppa-and-weak-pigeon.md)
- [Erdős–Rado sunflower lemma](../../../../Combinatorics/extremal-set-theory/intersecting-families/sunflower-lemma/exists-is-delta-system.md)
- [Search problems: FNP, FP and TFNP](../../total-search-problems/search-problems-fnp-fp-and-tfnp.md)

## Proof depends on

- [Finite Ramsey theorem for pairs](../../../../Combinatorics/ramsey-theory/structural-ramsey/ramsey-two-uniform.md)

## Sources

- Amol Pasarkar, Christos Papadimitriou and Mihalis Yannakakis, "Extremal Combinatorics, Iterated Pigeonhole Arguments and Generalizations of PPP", ITCS (2023), arXiv:2209.07625.
