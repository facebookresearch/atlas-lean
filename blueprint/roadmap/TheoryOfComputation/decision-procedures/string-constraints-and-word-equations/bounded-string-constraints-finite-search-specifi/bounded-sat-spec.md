# Bounded-search satisfiability specification

Let $\alpha$ be a finite alphabet. Let $V$ be a set of variables. A string-constraint formula over $\alpha$ with variables in $V$ is built from atoms using conjunction, disjunction, true and false (there is no negation); an atom is an equality $t_1 = t_2$ of terms, a membership of a term in the language of a regular expression, or a length bound $|t| \le k$ or $|t| \ge k$, where terms are built from constant words and variables by concatenation and by applying a letter-to-word substitution $h : \alpha \to \alpha^*$; a substitution $\sigma : V \to \alpha^*$ satisfies a formula when it holds after evaluating every term under $\sigma$. An association list is a finite list $(v_1, w_1), \dots, (v_k, w_k)$ of pairs of a variable and a word over $\alpha$; the lookup of a variable $v$ in it is $w_j$ for the least $j$ with $v_j = v$, and the empty word if $v$ is none of the $v_j$. For a finite list $vs = v_1 \cdots v_k$ of variables and $B \in \mathbb{N}$, the bounded assignment enumeration for $vs$ and $B$ is the list of all association lists $(v_1, w_1), \dots, (v_k, w_k)$ with words $w_j$ over $\alpha$ of length at most $B$ (keys exactly $v_1, \dots, v_k$ in this order), each such list occurring once.

For a list $vs$ of variables, a formula $\varphi$ and $B \in \mathbb{N}$, the bounded-search test returns
true if and only if some association list $l$ in the bounded assignment enumeration for $vs$ and $B$ is
such that the substitution sending each variable to its lookup in $l$ satisfies $\varphi$.

It is a specification by finite search, defined by a choice of enumeration of the finite alphabet rather
than by an algorithm.
