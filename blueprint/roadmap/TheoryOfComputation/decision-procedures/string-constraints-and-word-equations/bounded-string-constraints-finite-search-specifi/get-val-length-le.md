# Lookup inherits the length bound on values

Let $\alpha$ be an alphabet and $V$ a set of variables. An association list is a finite list $(v_1, w_1), \dots, (v_k, w_k)$ of pairs of a variable and a word over $\alpha$; the lookup of a variable $v$ in it is $w_j$ for the least $j$ with $v_j = v$, and the empty word if $v$ is none of the $v_j$. Let $l$ be an association list all of whose
words have length at most $B$, and let $v$ be a variable occurring as a key of $l$. Then the lookup of $v$
in $l$ has length at most $B$.
