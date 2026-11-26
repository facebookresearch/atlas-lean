# NUMERICAL 3-DIMENSIONAL MATCHING as a decision problem

The decision problem NUMERICAL
3-DIMENSIONAL MATCHING accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding (natural numbers in binary), to an instance $(A, B, C, t)$ that is well
formed and feasible: the lists $B$ and $C$ have the same length $n$ as the list $A$, and there
are permutations $p$ and $q$ of the numbers $0$ through $n-1$ such that
$A_j + B_{p(j)} + C_{q(j)} = t$ for every $j < n$, with lists indexed from $0$. Every other
bitstring is rejected.
