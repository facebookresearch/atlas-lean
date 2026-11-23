# The SAT verifier verifies SAT

The SAT verifier verifies the SAT decision problem with
witness bound the polynomial $X$: for every list $x$ of Booleans, $x$ encodes a satisfiable CNF
formula if and only if there is a list $w$ of Booleans, of length at most the length of $x$, such
that the SAT verifier on $(x, w)$ returns true.

The intended witness lists values for the variables occurring in the decoded formula, in order of
occurrence; its length is the literal count, which is at most the input length.
