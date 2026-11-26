# A URM-computable partial function is partial recursive

Let $f$ be a partial function
from $\mathbb{N}$ to $\mathbb{N}$. Suppose some URM program has the following property for every
natural number $x$: started with $x$ in register $0$ and all other registers $0$, it halts
exactly when $f(x)$ is defined, and then it holds $f(x)$ in register $0$. Then $f$ is partial
recursive.

The URM evaluation is the unbounded search for the first halting step of the coded execution.
