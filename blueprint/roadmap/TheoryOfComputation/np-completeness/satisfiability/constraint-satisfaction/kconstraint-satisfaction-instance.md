# Instances given by a variable count, conjunctive terms and a threshold

An instance is a triple $(n, C, K)$: a natural number $n$, a list $C$ of **conjunctive** terms, each a list of literals $(x, b)$ with a natural variable label $x$ and a sign $b$, and a natural threshold $K$. The labels need not be below $n$, and the term widths are not bounded by the type. The same triples are the instances of k-CONSTRAINT SATISFACTION and of MINIMUM 3DNF SATISFIABILITY; both count satisfied terms with the same function, and their upper or lower bounds and width tests are separate predicates.
