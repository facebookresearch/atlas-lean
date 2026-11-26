# Variables occurring in a string formula

Let $\alpha$ be an alphabet and $V$ a set of variables. String terms over $\alpha$ with variables in $V$ are built from constant words $w \in \alpha^*$, variables $x \in V$, concatenations $t_1 \cdot t_2$ and morphism applications $h(t)$, where $h$ is a map $\alpha \to \alpha^*$ extended letter by letter to words. An atom is an equation $t_1 = t_2$, a membership $t \in L(e)$ for a regular expression $e$ over $\alpha$, or a length bound $|t| \le k$ or $|t| \ge k$ with $k \in \mathbb{N}$, where $t, t_1, t_2$ are terms. Formulas are built from atoms, true and false by conjunction and disjunction (there is no negation). The variables of an atom are the variables of the terms in it. The list of variables of a formula is defined recursively: for an atom, the variables of
the atom; for $\varphi \wedge \psi$ and $\varphi \vee \psi$, the variables of $\varphi$ followed by those of
$\psi$; for true and false, the empty list (repetitions allowed).
