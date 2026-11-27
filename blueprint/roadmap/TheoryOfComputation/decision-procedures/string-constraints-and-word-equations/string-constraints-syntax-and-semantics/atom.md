# String constraint atom

Let $\alpha$ be an alphabet and $V$ a set of variables. String terms over $\alpha$ with variables in $V$ are built from constant words $w \in \alpha^*$, variables $x \in V$, concatenations $t_1 \cdot t_2$ and morphism applications $h(t)$, where $h$ is a map $\alpha \to \alpha^*$ extended letter by letter to words. A string atom over $\alpha$ with variables in $V$ is one of: a word equation $t_1 = t_2$ between two
terms; a regular-membership constraint $t \in L(e)$ for a term $t$ and a regular expression $e$ over
$\alpha$; a length bound $|t| \le k$; or a length bound $|t| \ge k$, with $t$ a term and $k \in \mathbb{N}$.
