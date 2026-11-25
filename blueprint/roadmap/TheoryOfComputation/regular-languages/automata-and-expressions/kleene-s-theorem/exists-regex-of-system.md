# Solving a system of language equations

Let $\alpha$ be an alphabet and $n \in \mathbb{N}$. A language over $\alpha$ is regex-denoted if it is the language matched by some regular expression over $\alpha$ (regular expressions being built from $0$, $1$ and single letters by sum, concatenation and Kleene star). Let $A_{ij}$, $B_i$ and $X_i$ ($0 \le i, j < n$) be languages over
$\alpha$ such that every $A_{ij}$ and every $B_i$ is regex-denoted, no $A_{ij}$ contains the empty word, and

$$X_i = \bigcup_{j < n} A_{ij} X_j \cup B_i \qquad \text{for all } i < n.$$

Then every $X_i$ is regex-denoted.

The last unknown is eliminated by Arden's lemma and the reduced system is solved by induction on $n$.
