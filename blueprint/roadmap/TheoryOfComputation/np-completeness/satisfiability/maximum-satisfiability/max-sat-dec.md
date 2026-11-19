# MAXIMUM SATISFIABILITY as a decision problem

The decision problem MAXIMUM SATISFIABILITY
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of
MAX-SAT instances, to an instance $(n, \varphi, K)$ that is well formed (every literal of
$\varphi$ has variable index less than $n$) and feasible (some assignment of truth values to the
$n$ variables satisfies at least $K$ of the clauses of $\varphi$, counted with multiplicity).
Bitstrings that do not decode, and bitstrings that decode to instances that are not well formed,
are rejected.
