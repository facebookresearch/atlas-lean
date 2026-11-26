# Splitter count of newly added splitters

Let $\Sigma$ be an alphabet listed in a fixed order and $Q$ a set. For $C \subseteq Q$ and $a \in \Sigma$, $\mathrm{pre}(C, a) = \{q \in Q : \delta(q, a) \in C\}$; a set $X$ splits a block $D$ if $D \cap X$ and $D \setminus X$ are both nonempty; and $\mathrm{sm}(A, B)$ is $A$ if $|A| \le |B|$ and $B$ otherwise. For a waiting list $W$ (a finite list of splitters $(C, b)$ with $C \subseteq Q$, $b \in \Sigma$), a set $X$ and a block $D$, the new splitters are, for each letter $b$ in order, the two entries $(D \cap X, b), (D \setminus X, b)$ if $(D, b)$ occurs in $W$, and the single entry $(\mathrm{sm}(D \cap X, D \setminus X), b)$ otherwise. For $q \in Q$, $b \in \Sigma$ and a list $W$ of splitters, the splitter count $\mathrm{cnt}(q, b, W)$ is the number of entries $(C, b')$ of $W$, counted with multiplicity, with $b' = b$ and $q \in C$. For $q \in Q$, $b \in \Sigma$, a waiting
list $W$ and sets $X, D \subseteq Q$, the splitter count of $q$ and $b$ in the new splitters for $W$, $X$ and $D$ is:
if $(D, b)$ occurs in $W$, $1$ if $q \in D$ and $0$ otherwise; if not, $1$ if $q \in \mathrm{sm}(D \cap X,
D \setminus X)$ and $0$ otherwise.
