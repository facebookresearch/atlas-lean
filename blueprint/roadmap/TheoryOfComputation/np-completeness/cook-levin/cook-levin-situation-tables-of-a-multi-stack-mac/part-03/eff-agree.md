# The symbolic effect of a statement agrees with the real step

Let $q$ be a statement tree
of a multi-stack machine, $d \in \mathbb{N}$, and $S_0$ an assignment of a list $S_0(k)$ to each
stack $k$. Let $v$ be a state, $P$ an assignment of a list $P(k)$ to each stack, and $c$ an
assignment of a natural number $c(k)$ to each stack with $c(k) + \operatorname{ops}(q) \le d$ for
every $k$. Then running $q$ from state $v$ on the stacks whose stack $k$ is $P(k)$ followed by
$S_0(k)$ with its first $c(k)$ symbols removed gives the configuration obtained by applying to
$S_0$ the effect of $q$ computed from $v$, $P$, $c$ and the depth-$d$ windows of the $S_0(k)$.

Here $\operatorname{ops}(q)$ is the largest number of push, peek and pop nodes on a path of $q$,
so the hypothesis keeps every read inside the windows.
