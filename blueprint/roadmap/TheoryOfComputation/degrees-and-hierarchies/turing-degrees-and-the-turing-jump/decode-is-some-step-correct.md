# The definedness step function is correct

For a natural number $n$, let $b_n$ be $1$ if
the computable decoder returns an oracle code on $n$, and $0$ otherwise. For every natural number
$m$, the one-step function of the course-of-values recursion for definedness, applied to the list
$(b_0, b_1, \dots, b_{m-1})$, returns $b_m$.

## Sources

- Rogers, *Theory of Recursive Functions and Effective Computability*, §1.6 (Gödel numberings; decoding).
