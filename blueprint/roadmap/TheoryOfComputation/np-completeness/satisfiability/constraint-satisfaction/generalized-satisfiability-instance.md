# Instances of GENERALIZED SATISFIABILITY

An instance is a pair of a natural number $n$ and a list of triples $(k, R, C)$: a natural number $k$, a list $R$ of Boolean lists, read as the tuples of a relation, and a list $C$ of lists of natural variable labels. Nothing in the type ties the rows of $R$ or the members of $C$ to length $k$, or the labels to $n$; those conditions belong to [validation](well-formed-2-3.md). Feasibility asks for an assignment under which every listed member of each $C$, mapped by the assignment, is a listed row of the corresponding $R$, with no length filter.
