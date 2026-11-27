# Uniform sampling by rejection on the randomized word RAM

On the randomized word RAM, the loop that draws $b=\lceil\log_2 m\rceil$ uniform bits and repeats until the resulting value is below $m$, for $1\le m\le 2^{w}$, is the uniform-integer case of fair-bit block rejection sampling, with the blocks drawn by the machine's random instructions. More generally, let $T$ be the number of iterations of a while loop whose body, given any history of earlier iterations, exits with probability at least $q>0$. Then $\Pr[T>t]\le(1-q)^{t}$ for every $t\ge0$, so $T$ is finite with probability $1$, and $\mathbb{E}[T]\le 1/q$.

## Proof sketch

By induction on $t$, $\Pr[T>t+1]=\Pr[T>t]\cdot\Pr[\text{no exit at iteration }t+1\mid T>t]\le(1-q)^{t+1}$. Then $\mathbb{E}[T]=\sum_{t\ge0}\Pr[T>t]\le\sum_{t\ge0}(1-q)^t=1/q$.

## Depends on

- [Randomized word RAM](../../../ComputerScience/sorting-and-searching/word-ram-integer-algorithms/randomized-word-ram.md)
- [Fair-bit block rejection sampling: exact law, capped trials and expected cost](../../../ComputerScience/algebraic-and-numerical-algorithms/exact-sampling-from-coin-flips/fair-bit-block-rejection-sampling.md)

## Sources

- Torben Hagerup, "Sorting and Searching on the Word RAM", STACS 98, 1998.
