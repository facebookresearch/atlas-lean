# Lookup recovers the assignment from its association list

Let $\alpha$ be an alphabet and $V$ a set of variables. An association list is a finite list $(v_1, w_1), \dots, (v_k, w_k)$ of pairs of a variable and a word over $\alpha$; the lookup of a variable $v$ in it is $w_j$ for the least $j$ with $v_j = v$, and the empty word if $v$ is none of the $v_j$. Let $\sigma : V \to \alpha^*$, let $vs = v_1
\cdots v_k$ be a list of variables and let $v$ occur in $vs$. Then the lookup of $v$ in the association
list $(v_1, \sigma(v_1)), \dots, (v_k, \sigma(v_k))$ is $\sigma(v)$.
