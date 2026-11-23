# Variables occurring in a string term

Let $\alpha$ be an alphabet and $V$ a set of variables. String terms over $\alpha$ with variables in $V$ are built from constant words $w \in \alpha^*$, variables $x \in V$, concatenations $t_1 \cdot t_2$ and morphism applications $h(t)$, where $h$ is a map $\alpha \to \alpha^*$ extended letter by letter to words. The list of variables of a term is defined recursively: empty for a constant word; the one-element
list $x$ for a variable $x$; the variables of $t_1$ followed by those of $t_2$ for $t_1 \cdot t_2$; and the
variables of $t$ for $h(t)$. Repetitions are allowed.
