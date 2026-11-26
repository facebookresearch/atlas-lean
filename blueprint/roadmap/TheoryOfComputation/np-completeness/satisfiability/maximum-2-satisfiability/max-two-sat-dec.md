# MAXIMUM 2-SATISFIABILITY as a decision problem

The decision problem MAXIMUM
2-SATISFIABILITY accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding of MAX-2SAT instances, to an instance $(n, \varphi, K)$ that is well formed (every clause
of $\varphi$ has at most two literals, and every literal has variable index less than $n$) and
feasible (some assignment of truth values to the $n$ variables satisfies at least $K$ of the
clauses of $\varphi$, counted with multiplicity). Bitstrings that do not decode, and bitstrings
that decode to instances that are not well formed, are rejected.
