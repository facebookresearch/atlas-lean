# SINGLE-MACHINE WEIGHTED COMPLETION WITH PRECEDENCE as a decision problem

The decision
problem accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding,
to an instance $(J, P, K)$ that is well formed and feasible: every precedence pair in $P$ consists
of two distinct job indices of $J$, and some ordering of all the jobs that puts the first job of
every precedence pair before the second has total weighted completion time at most $K$.
Bitstrings that do not decode to an instance are rejected.
