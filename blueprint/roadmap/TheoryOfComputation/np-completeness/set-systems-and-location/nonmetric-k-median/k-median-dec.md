# The k-MEDIAN decision problem

**The k-MEDIAN decision problem.** k-MEDIAN (generalized, nonmetric) is the decision problem
that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to
a k-median instance $(d, K, B)$ that is well formed and feasible. That is, $d$ has rows
$d_0, \dots, d_{n-1}$ (the clients) of a common length $m$ (the locations), and there are a set
$S \subseteq \{0, \dots, m-1\}$ of at most $K$ locations and a choice of $a(c) \in S$ for each
client $c < n$ with $\sum_{c < n} d_{c, a(c)} \le B$. Bitstrings that do not decode are
rejected.
