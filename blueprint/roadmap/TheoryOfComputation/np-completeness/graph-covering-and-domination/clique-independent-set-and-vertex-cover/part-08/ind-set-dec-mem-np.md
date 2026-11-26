# INDEPENDENT-SET is in NP

The decision problem [INDEPENDENT-SET](../part-01/ind-set-dec.md), which accepts exactly the
encodings $1^k\,0\,1^n\,0\,b$ of a number $k$ and a graph on $\{0, \dots, n - 1\}$ given by one
pair bit for each pair $i < j < n$ such that the graph has an independent set of exactly $k$
vertices, belongs to NP: there are a polynomial $p$ with natural-number coefficients and a
polynomial-time computable verifier $R$ such that INDEPENDENT-SET accepts $x$ exactly when
$R(x, w)$ holds for some bit string $w$ with $|w| \le p(|x|)$.
