# Enumerated lists over distinct variables are recovered from lookups

Let $\alpha$ be a finite alphabet. Let $V$ be a set of variables. An association list is a finite list $(v_1, w_1), \dots, (v_k, w_k)$ of pairs of a variable and a word over $\alpha$; the lookup of a variable $v$ in it is $w_j$ for the least $j$ with $v_j = v$, and the empty word if $v$ is none of the $v_j$. For a finite list $vs = v_1 \cdots v_k$ of variables and $B \in \mathbb{N}$, the bounded assignment enumeration for $vs$ and $B$ is the list of all association lists $(v_1, w_1), \dots, (v_k, w_k)$ with words $w_j$ over $\alpha$ of length at most $B$ (keys exactly $v_1, \dots, v_k$ in this order), each such list occurring once.

Let $vs = v_1 \cdots v_k$ be a list of pairwise distinct variables, $B \in \mathbb{N}$, and $l$ an
association list in the bounded assignment enumeration for $vs$ and $B$. Then $l$ equals $(v_1,
\lambda(v_1)), \dots, (v_k, \lambda(v_k))$, where $\lambda(v)$ is the lookup of $v$ in $l$.
