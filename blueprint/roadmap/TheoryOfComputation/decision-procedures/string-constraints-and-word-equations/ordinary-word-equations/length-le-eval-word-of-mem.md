# Occurring variable's image is no longer than the evaluated word

Let $\alpha$ be an alphabet of constants and $V$ a set of variables, disjoint from $\alpha$. A pattern is a finite word over $\alpha \cup V$, and for a substitution $\sigma : V \to \alpha^*$ the evaluation $\sigma(w)$ of a pattern $w$ is the word over $\alpha$ obtained by replacing each variable $x$ in $w$ by $\sigma(x)$. Let $\sigma : V \to \alpha^*$, let $w$ be a pattern and let $x$ be a variable occurring in $w$. Then
$|\sigma(x)| \le |\sigma(w)|$.

Each occurrence of $x$ contributes the block $\sigma(x)$ to $\sigma(w)$, also when other images are empty.
