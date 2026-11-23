# Size of the bounded assignment enumeration

Let $\alpha$ be a finite alphabet. Let $V$ be a set of variables. For a finite list $vs = v_1 \cdots v_k$ of variables and $B \in \mathbb{N}$, the bounded assignment enumeration for $vs$ and $B$ is the list of all association lists $(v_1, w_1), \dots, (v_k, w_k)$ with words $w_j$ over $\alpha$ of length at most $B$ (keys exactly $v_1, \dots, v_k$ in this order), each such list occurring once.

For every list $vs$ of variables and every $B \in \mathbb{N}$, the bounded assignment enumeration for $vs$
and $B$ has exactly $N_B^{|vs|}$ entries, where $N_B = \sum_{n=0}^{B} |\alpha|^n$ is the number of words
over $\alpha$ of length at most $B$.

This counts association lists; it is the number of distinct assignments of the variables of $vs$ when
these are pairwise distinct.
