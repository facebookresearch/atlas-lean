# Bounded split test

Given Boolean tests $f$ and $g$ on words over $\sigma$, a word $w$ and
a natural number $n$, the split test is the Boolean value that is true exactly when there is some
$i < n$ such that $f$ is true on the prefix of $w$ of length $\min(i, |w|)$ and $g$ is true on
the remaining suffix of $w$.
