# Weighted radius at least $K$ is NP-complete for trees

Statement: the decision problem WEIGHTED DIAMETER with radius $K$ or greater for trees belongs to NP, and every decision problem $L$ in NP is polynomial-time many-one reducible to it: there is a function $f$ from bitstrings to bitstrings, computable in polynomial time, such that $x \in L$ exactly when $f(x)$ is accepted, for every bitstring $x$.

An instance consists of a tree $G = (V, E)$, a collection $C$ of $|E|$ not necessarily distinct non-negative integers, and a positive integer $K$; the question is whether there is a one-to-one assignment $f : E \to C$ such that, taking $f(e)$ as the length of edge $e$, for every vertex $v$ some vertex $u$ has every path from $v$ to $u$ of length at least $K$ (that is, $G$ has radius $K$ or greater).

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT65] WEIGHTED DIAMETER, p. 205, comment (credited to Perl and Zaks, 1978).
- Y. Perl and S. Zaks, "On the complexity of edge labelings for trees", *Theoretical Computer Science* 19 (1982), 1–16, <https://doi.org/10.1016/0304-3975(82)90011-1>.
