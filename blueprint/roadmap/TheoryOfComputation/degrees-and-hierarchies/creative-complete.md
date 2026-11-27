# Creative sets are many-one complete for the RE sets

The following holds. Let $A \subseteq \mathbb{N}$ be creative: $A$ is recursively enumerable and its complement is productive, meaning there is a partial recursive function $f$ such that for every $e$ with $W_e \subseteq \mathbb{N} \setminus A$, the value $f(e)$ is defined, $f(e) \notin A$ and $f(e) \notin W_e$ (here $W_e$ is the $e$-th recursively enumerable set). Then every recursively enumerable set $B \subseteq \mathbb{N}$ is many-one reducible to $A$: there is a computable $g : \mathbb{N} \to \mathbb{N}$ with $n \in B \iff g(n) \in A$ for all $n$.

## Sources

- R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Ch. II §4, p. 40 (complete, productive and creative sets).
- H. Rogers, *Theory of Recursive Functions and Effective Computability*, §8.4.
