# The Turing jump

For a predicate $P$ on $\mathbb{N}$, the Turing jump $P'$ is the
predicate that holds at $n$ exactly when the $n$-th oracle code in the effective enumeration of
oracle codes, evaluated with the oracle that answers $1$ at $m$ if $P(m)$ holds and $0$ otherwise,
halts on input $n$. Thus $P'$ is the diagonal halting set of the universal oracle machine with
oracle $P$.

## Sources

- Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 2.1 (the jump).
