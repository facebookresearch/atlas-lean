# The Turing jump

For a predicate $P$ on $\mathbb{N}$, the Turing jump $P'$ is the
predicate that holds at $n$ exactly when the $n$-th oracle code in the effective enumeration of
oracle codes, evaluated with the oracle that answers $1$ at $m$ if $P(m)$ holds and $0$ otherwise,
halts on input $n$. Thus $P'$ is the diagonal halting set of the universal oracle machine with
oracle $P$.

## Sources

- R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987 (the jump).
