# Soundness and completeness of the bounded-search specification

Let $\alpha$ be a finite alphabet. Let $V$ be a set of variables. A string-constraint formula over $\alpha$ with variables in $V$ is built from atoms using conjunction, disjunction, true and false (there is no negation); an atom is an equality $t_1 = t_2$ of terms, a membership of a term in the language of a regular expression, or a length bound $|t| \le k$ or $|t| \ge k$, where terms are built from constant words and variables by concatenation and by applying a letter-to-word substitution $h : \alpha \to \alpha^*$; a substitution $\sigma : V \to \alpha^*$ satisfies a formula when it holds after evaluating every term under $\sigma$. An association list is a finite list $(v_1, w_1), \dots, (v_k, w_k)$ of pairs of a variable and a word over $\alpha$; the lookup of a variable $v$ in it is $w_j$ for the least $j$ with $v_j = v$, and the empty word if $v$ is none of the $v_j$.

Let $vs$ be a finite list of variables containing every variable occurring in a formula $\varphi$, and
let $B \in \mathbb{N}$. The bounded-search test (true if and only if, for some association list $l$ with
keys $vs$ and values of length at most $B$, the substitution $v \mapsto$ lookup of $v$ in $l$ satisfies
$\varphi$) returns true if and only if there is a substitution $\sigma : V \to \alpha^*$ with
$|\sigma(v)| \le B$ for every $v$ in $vs$ that satisfies $\varphi$.
