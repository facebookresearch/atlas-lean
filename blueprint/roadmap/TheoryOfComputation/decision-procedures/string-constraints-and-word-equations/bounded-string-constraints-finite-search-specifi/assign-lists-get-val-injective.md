# Enumerated lists over distinct variables give distinct assignments

Let $\alpha$ be a finite alphabet. Let $V$ be a set of variables. An association list is a finite list $(v_1, w_1), \dots, (v_k, w_k)$ of pairs of a variable and a word over $\alpha$; the lookup of a variable $v$ in it is $w_j$ for the least $j$ with $v_j = v$, and the empty word if $v$ is none of the $v_j$. For a finite list $vs = v_1 \cdots v_k$ of variables and $B \in \mathbb{N}$, the bounded assignment enumeration for $vs$ and $B$ is the list of all association lists $(v_1, w_1), \dots, (v_k, w_k)$ with words $w_j$ over $\alpha$ of length at most $B$ (keys exactly $v_1, \dots, v_k$ in this order), each such list occurring once.

Let $vs$ be a list of pairwise distinct variables, $B \in \mathbb{N}$, and $l_1, l_2$ association lists in
the bounded assignment enumeration for $vs$ and $B$. If the lookups of every variable of $vs$ in $l_1$
and in $l_2$ agree, then $l_1 = l_2$.

Without distinctness this fails: a repeated variable lets a later entry be hidden by an earlier one.
