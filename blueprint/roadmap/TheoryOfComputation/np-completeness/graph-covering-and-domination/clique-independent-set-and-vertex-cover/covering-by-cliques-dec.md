# COVERING BY CLIQUES as a decision problem

The COVERING BY CLIQUES decision problem accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of instances, to a well-formed, feasible instance of COVERING BY CLIQUES; it rejects every bitstring that does not decode to an instance.

The same language is INTERSECTION GRAPH BASIS ([GT59]) as a decision problem: both use the same graph on the same encoded triple, the same validation, decoder and rejection branch, so they accept exactly the same bitstrings.
