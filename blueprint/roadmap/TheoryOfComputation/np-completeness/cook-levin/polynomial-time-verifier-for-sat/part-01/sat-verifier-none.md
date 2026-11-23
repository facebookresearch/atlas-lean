# The SAT verifier rejects undecodable inputs

For all lists of Booleans $x$ and $w$, if
the complete CNF decoder fails on $x$, then the SAT verifier on $(x, w)$ returns false at
declared time cost $0$.
