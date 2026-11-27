# Uniform sampling by rejection on the randomized word RAM

For $1\le m\le 2^{w}$, the loop that draws $b=\lceil\log_2 m\rceil$ uniform bits and repeats until the resulting value is below $m$ terminates with probability $1$, outputs a uniformly distributed value in $\{0,\dots,m-1\}$, and has expected number of iterations $2^{b}/m<2$. More generally, a while loop whose body exits with probability at least $q>0$ independently in each iteration has a geometric exit law with expected iteration count at most $1/q$.

## Proof sketch

Each iteration exits with probability $m/2^{b}>1/2$, independently; conditioned on exit the value is uniform on $[0,m)$. The number of iterations is geometric.

## Depends on

- [Randomized word RAM](../../../ComputerScience/sorting-and-searching/word-ram-integer-algorithms/randomized-word-ram.md)

## Proof depends on

- [Rejection sampling outputs the target law](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/rejection-sampling/tsum-rejections-mul-trial.md)

## Sources

- Torben Hagerup, "Sorting and Searching on the Word RAM", STACS 98, 1998.
