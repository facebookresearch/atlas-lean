# Association-list lookup defaulting to the empty word

Let $\alpha$ be an alphabet and $V$ a set of variables. For an association list $(v_1, w_1), \dots, (v_k,
w_k)$ of variables and words over $\alpha$, the lookup of a variable $v$ is defined recursively: it is the
empty word for the empty list, and for a list with first pair $(v_1, w_1)$ it is $w_1$ if $v = v_1$ and
otherwise the lookup of $v$ in the rest. So it is $w_j$ for the least $j$ with $v_j = v$, and the empty
word if there is none.
