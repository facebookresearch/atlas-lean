# Rice's theorem for acceptable numberings

Let $\varphi$ assign to each natural number $e$
a partial function $\varphi_e : \mathbb{N} \rightharpoonup \mathbb{N}$, and suppose that every
$\varphi_e$ is partial computable, that the universal function $(e, n) \mapsto \varphi_e(n)$ is
partial computable, that every partial computable function
$f : \mathbb{N} \rightharpoonup \mathbb{N}$ equals $\varphi_e$ for some $e$, and that for every
partial computable $g : \mathbb{N} \times \mathbb{N} \rightharpoonup \mathbb{N}$ there is a total
computable $s : \mathbb{N} \to \mathbb{N}$ with $\varphi_{s(e)}(n) = g(e, n)$ for all $e$ and $n$.
Let $C \subseteq \mathbb{N}$ be a set of indices closed under extensional equality, that is, if
$\varphi_a(n) = \varphi_b(n)$ for all $n$, then $a \in C$ if and only if $b \in C$; and suppose
that $C$ is neither empty nor all of $\mathbb{N}$. Then there is no total computable
$d : \mathbb{N} \to \mathbb{N}$ such that, for every $e$, $e \in C$ if and only if $d(e) = 1$,
and $e \notin C$ if and only if $d(e) = 0$.

Proof: The standard argument first derives Kleene's recursion theorem for the acceptable
numbering, then diagonalizes a putative decider, following Rice (1953), Rogers §11.2, and
Soare II.3.1.

## Sources

- H. G. Rice, *Classes of recursively enumerable sets and their decision problems*, Transactions of the American Mathematical Society 74(2) (1953), 358-366.
