# Termination probability of the binary branching grammar from tree cylinders

Let $0 \le p \le 1$. On $\Omega = \{0, 1\}^{\{0,1\}^*}$, with one coordinate for each finite binary address, let the coordinates be independent with $P(\omega(a) = 1) = p$: $\omega(a) = 1$ means the node at address $a$ rewrites $S \to SS$, and $0$ means it rewrites $S \to a$. A finite derivation tree $t$ determines a cylinder $C_t$, the set of $\omega$ that agree with $t$ at its internal and leaf addresses and are unconstrained elsewhere; then $P(C_t) = p^{i(t)}(1-p)^{\ell(t)}$ with $i(t)$ internal nodes and $\ell(t) = i(t) + 1$ leaves, and distinct finite trees have disjoint cylinders. Let $T_h$ be the event that the derivation from the root terminates within depth $h$; it is the finite disjoint union of the cylinders of the trees of depth at most $h$, a single leaf having depth $1$ (equivalently, of the trees all of whose addresses have length less than $h$), and $q_h = P(T_h)$ satisfies $q_0 = 0$, $q_{h+1} = (1-p) + pq_h^2$. Since $T_h$ increases, the termination probability $P(\bigcup_h T_h) = \lim_h q_h$ is the least root of $q = (1-p) + pq^2$ in $[0, 1]$, equal to $1$ for $p \le 1/2$ and to $(1-p)/p$ for $p > 1/2$. For $p = 2/3$ it is $1/2$, and so is the nontermination probability.

## Proof depends on

- [Limit of generating-function iterates is the least fixed point](../../../Probability/branching-processes/galton-watson-process/is-least-i-sup-iterate-pgf-zero.md): the iterates of the generating function $s \mapsto (1-p) + ps^2$ from $0$ increase to its least fixed point in $[0, 1]$.

## Sources

- *M375T/M396C: Topics in Complex Networks*, lecture 3 notes, University of Texas at Austin, Theorem 3.1, <https://web.ma.utexas.edu/users/rav/ComplexNetworks/ComplexNetworks.Lecture03.Notes.pdf>
