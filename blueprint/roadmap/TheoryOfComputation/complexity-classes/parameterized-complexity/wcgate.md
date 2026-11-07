# Encoded gates for weighted circuit satisfiability

An encoded gate is a pair $(k, r)$ of a
natural number $k$, its kind, and a list $r$ of natural numbers, its references.

Gates are read as in the shared (kind, references) encoding of flat Boolean circuits on $n$
inputs: $(0, [i])$ is the input variable $x_i$ when $i < n$, $(1, [b])$ is the constant that is
true exactly when $b = 1$, $(2, [a])$ is the negation of gate $a$, and $(3, r)$ and $(4, r)$ are
the AND and the OR of the gates listed in $r$; every other pair, including $(0, [i])$ with
$i \ge n$ and $(2, r)$ with $r$ not of length one, evaluates to false.
