# The costed progress-measure verifier

It computes the same result
as `verifyProgress`, together with the number of atomic component
comparisons (plus one move test per edge) it actually evaluates: the
traversal that computes the result is the traversal that accumulates the
cost, so the cost is not a separately computed cardinality. Source:
M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301.
