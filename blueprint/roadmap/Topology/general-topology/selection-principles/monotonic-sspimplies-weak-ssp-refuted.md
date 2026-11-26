# The monotonic sequence selection property does not imply the weak one

There is a set of reals $X$ such that $C_p(X)$ has the monotonic sequence selection property but not the weak sequence selection property; Tsaban's Milestone Problem 15.4 has a negative answer. For a topological space $X$, $C_p(X)$ is the space of continuous functions $X \to \mathbb{R}$ with the topology of pointwise convergence (the subspace topology of the product $\mathbb{R}^X$), and $\mathbf{0}$ is the constant zero function. $C_p(X)$ has the monotonic sequence selection property when for every family $(f^n_k)_{n,k \in \mathbb{N}}$ in $C_p(X)$ such that each sequence $(f^n_k)_k$ converges to $\mathbf{0}$ and is non-increasing ($f^n_{k+1}(x) \le f^n_k(x)$ for all $k$ and $x$) there are indices $k_n$ with $f^n_{k_n} \to \mathbf{0}$. $C_p(X)$ has the weak sequence selection property when for every family $(f^n_k)_{n,k \in \mathbb{N}}$ in $C_p(X)$ such that each sequence $(f^n_k)_{k}$ converges to $\mathbf{0}$ there are indices $k_n$ with $\mathbf{0}$ in the closure of $\{f^n_{k_n} : n \in \mathbb{N}\}$.

For $X = [0,1]$, monotone pointwise convergence to $\mathbf{0}$ is uniform by Dini's theorem, which gives the monotonic property, while Sakai proved that the weak property forces $X$ to be zero-dimensional.

## Sources

- B. Tsaban, Selection principles in mathematics: A milestone of open problems, Note di Matematica 22 (2003/2004), arXiv:math/0312182, Problem 15.4 (M. Scheepers, Proc. Amer. Math. Soc. 125 (1997), Problem 2); resolution: M. Sakai, The sequence selection properties of C_p(X), Topology Appl. 154 (2007), 552-560, doi:10.1016/j.topol.2006.07.008.
