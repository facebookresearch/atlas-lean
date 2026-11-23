# Newman's theorem

A (deterministic) protocol is a finite binary tree whose leaves carry output bits and whose internal nodes are owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$; on inputs $(x, y)$ the run follows the announced bits from the root to a leaf, whose bit is the output, and the depth is the maximal number of bits announced along a root-to-leaf path. A public-coin protocol with a finite set $R$ of random strings is a family $(p_r)_{r \in R}$ of protocols; its cost is the maximum of the depths of the $p_r$ ($0$ if $R$ is empty). For nonempty $R$, its error probability for $f : X \times Y \to \{0, 1\}$ at $(x, y)$ is the fraction $|\{r \in R : p_r \text{ outputs a value other than } f(x, y) \text{ on } (x, y)\}| / |R|$. For a protocol $p$ in which Alice holds $(x, a)$ and Bob holds $(y, b)$, with $a$ and $b$ ranging
over nonempty finite sets $R_A$ and $R_B$ of private random strings, the private error probability for $g$
at $(x, y)$ is the fraction of pairs $(a, b) \in R_A \times R_B$ on which $p$ outputs a value other than
$g(x, y)$.

There is a constant $C_0 \in \mathbb{R}$ such that for every $n \ge 1$, every $\varepsilon$ with $0 <
\varepsilon \le 1/2$, every $g : \{0,1\}^n \times \{0,1\}^n \to \{0, 1\}$, and every public-coin protocol with a
nonempty finite set of random strings whose error probability for $g$ is at most $\varepsilon$ at every
input pair, there are nonempty finite sets $R_A, R_B$ and a protocol $p$ for inputs $\{0,1\}^n \times R_A$
and $\{0,1\}^n \times R_B$ such that the depth of $p$ is at most $c + \log_2(n/\varepsilon^2) + C_0$, where $c$
is the cost of the public-coin protocol, and the private error probability of $p$ for $g$ is at most
$2\varepsilon$ at every input pair.

Some upper bound on $\varepsilon$ is needed: for large
$\varepsilon$ a cost-$0$ protocol meets the hypothesis while $\log_2(n/\varepsilon^2)$ is negative.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Theorem 3.5, attributed there to Newman.
- I. Newman, "Private vs. common random bits in communication complexity", *Information Processing Letters* 39 (1991), 67–71.
