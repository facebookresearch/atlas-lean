# The SET COVER decision problem

SET COVER is the decision problem that accepts a bitstring
$x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a set-cover instance
$(n, C, K)$ that is both well formed and feasible: every list in $C$ has no repeated entries and
only entries less than $n$, and some sublist of $C$ with at most $K$ entries contains every natural
number $y < n$ in one of its lists. Bitstrings that do not decode to a set-cover instance are
rejected.
