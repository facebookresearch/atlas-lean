# String formulas

Let $\alpha$ be an alphabet and $V$ a set of variables. String terms over $\alpha$ with variables in $V$ are built from constant words $w \in \alpha^*$, variables $x \in V$, concatenations $t_1 \cdot t_2$ and morphism applications $h(t)$, where $h$ is a map $\alpha \to \alpha^*$ extended letter by letter to words. An atom is an equation $t_1 = t_2$, a membership $t \in L(e)$ for a regular expression $e$ over $\alpha$, or a length bound $|t| \le k$ or $|t| \ge k$ with $k \in \mathbb{N}$, where $t, t_1, t_2$ are terms. String formulas over $\alpha$ with variables in $V$ are the positive Boolean combinations of atoms:
every atom is a formula, true and false are formulas, and if $\varphi$ and $\psi$ are formulas then so are
$\varphi \wedge \psi$ and $\varphi \vee \psi$. There is no negation, as in the positive fragment of SMT-LIB
assertions.
