# KÖNIG and ERDŐS–KO–RADO search problems are PPP-complete

**KÖNIG**: a circuit $P:\{0,1\}^n\to\{0,1\}^n\times\{0,1\}$ assigns each node a parent and a left/right bit, purportedly defining a rooted binary tree on $2^n$ nodes with given root $r$; output two distinct nodes with the same $P$-value, the root if $P(r)\ne r$, a node $s\ne r$ with $P(s)=s$, a node from which $n$ parent steps do not reach $r$, or a root path $a_0=r,a_1,\dots,a_n$ with $P(a_i)=a_{i-1}$ (finite König lemma). **ERDŐS–KO–RADO** ($k=2$): a circuit $F:\{0,1\}^n\to(\{0,1\}^n)^2$ describes $2^n$ two-element subsets of $\{0,1\}^n$; output an index with a repeated element, two indices with equal sets, or two indices with disjoint sets (by Erdős–Ko–Rado an intersecting family of 2-sets of a $2^n$-set has at most $2^n-1$ members). Both problems are PPP-complete, although their totality proofs are iterated-majority arguments like that of LONG CHOICE.

## Proof sketch

ERDŐS–KO–RADO hardness: from a COLLISION circuit $C$ set $F(x)=(0^n,C(x))$; sets never are disjoint, an invalid set means $C(x)=0^n$, and equal sets give a collision. Membership: if $F(0)$ and $F(1)$ are not already a solution they share exactly one element $b$; the reduction to COLLISION maps every set containing $b$ to its other element and treats the remaining cases so that a collision or a preimage of a reserved value yields equal, invalid or disjoint sets. For KÖNIG, both directions rest on indexing the nodes of a binary tree by bit strings describing root paths, which converts between parent functions and pigeonhole circuits.

## Depends on

- [LONG CHOICE and the class PLC of polynomial long choice for iterated pigeonhole arguments](long-choice-and-plc.md)

## Sources

- Amol Pasarkar, Christos Papadimitriou and Mihalis Yannakakis, "Extremal Combinatorics, Iterated Pigeonhole Arguments and Generalizations of PPP", ITCS (2023), arXiv:2209.07625.
