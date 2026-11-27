# Straight-line replaceAll constraints

Straight-line replaceAll constraints are conjunctions of single assignments $x = s \circ s'$ and $x = \mathrm{replaceAll}(s, p, s')$, each using only input variables or earlier assigned ones, together with regular-membership constraints; the pattern $p$ may be a variable or a regular expression, and the replacement may be a variable.

Fix a finite alphabet $\Sigma$, string variables ranging over $\Sigma^*$, and the [leftmost-longest replaceAll](leftmost-longest-replaceall.md) function. Terms and constraints are

$$
s ::= x \mid u, \qquad p ::= x \mid e, \qquad \varphi ::= x = s \circ s \mid x = \mathrm{replaceAll}(s, p, s) \mid \varphi \wedge \varphi, \qquad \psi ::= x \in e \mid \psi \wedge \psi,
$$

where $x$ is a variable, $u \in \Sigma^*$ a constant word and $e$ a regular expression over $\Sigma$: the $s$ are string terms, the $p$ pattern terms, $\varphi$ a *relational constraint* and $\psi$ a *regular constraint* (a conjunction, without negation). A pattern variable assigned a word $w$ is read as the regular expression denoting $\{w\}$, also when $w = \varepsilon$. A variable is a *source variable* of $\varphi$ if $\varphi$ has no conjunct $x = s_1 \circ s_2$ and no conjunct $x = \mathrm{replaceAll}(\cdot, \cdot, \cdot)$. A relational constraint is *straight-line* if it is $\bigwedge_{i=1}^m x_i = P_i$ with $x_1, \dots, x_m$ pairwise distinct and every variable of $P_i$ a source variable or one of $x_1, \dots, x_{i-1}$. The class $\mathrm{SL}[\mathrm{replaceAll}]$ consists of the formulas $\varphi \wedge \psi$ with $\varphi$ straight-line; satisfiability asks for an assignment of words to all variables under which every conjunct holds. The *single-letter*, *constant-string* and *regular-expression cases* are those where every pattern is a letter, a constant word, or a regular expression, respectively.

**Eliminating concatenation and constants.** With two letters $a, b \notin \Sigma$, a conjunct $x = s_1 \circ s_2$ is replaced by $x' = \mathrm{replaceAll}(ab, a, s_1) \wedge x = \mathrm{replaceAll}(x', b, s_2)$ with a fresh variable $x'$, over the alphabet $\Sigma \cup \{a, b\}$, and every original variable is constrained by $y \in \Sigma^*$, so that $s_1, s_2$ contain neither $a$ nor $b$ and the result is $s_1 s_2$. The new formula is satisfiable iff the old one is, by solutions agreeing on the original variables. A constant subject or replacement $u$ is likewise replaced by a fresh source variable constrained by $\in \{u\}$. The result is *replaceAll-only*: every conjunct is $x_i = \mathrm{replaceAll}(z, p_i, z')$ with variables $z, z'$ and a pattern term $p_i$ (unchanged by the elimination; a regular expression in the regular-expression case).

**Dependency graph.** For a replaceAll-only formula $C$ in the regular-expression case, the dependency graph $G_C$ has the variables as vertices and, for each conjunct $x_i = \mathrm{replaceAll}(z, e_i, z')$, an *l-edge* labelled $(l, e_i)$ from $x_i$ to the subject $z$ and an *r-edge* labelled $(r, e_i)$ from $x_i$ to the replacement $z'$; the two edges are distinct even when $z = z'$. $G_C$ is acyclic; its *depth* is the maximum number of edges on a path, $0$ if there are no edges.

## Depends on

- [Leftmost-longest replaceAll](leftmost-longest-replaceall.md)

## Proof depends on

None.

## Expansion

This is a definition. The source shows that concatenation is redundant (its Proposition 3.6) and then works with replaceAll-only formulas, defining the dependency graph for them; the guard $y \in \Sigma^*$ on original variables is needed because fresh letters alone do not constrain values: without it, $s_1 = b$, $s_2 = a$ would give $aa$ instead of $ba$. Likewise $x \in y^*$ is expressed as $x = \mathrm{replaceAll}(x', a, y) \wedge x' \in a^*$. When both pattern and replacement are constants, replaceAll is a finite-state transduction, so this logic covers that part of [straight-line string constraints](straight-line-string-constraints.md); with a variable replacement it does not.

## Sources

- T. Chen, Y. Chen, M. Hague, A. W. Lin and Z. Wu, "What is decidable about string constraints with the ReplaceAll function", Proceedings of the ACM on Programming Languages 2 (POPL), Article 3, 2018, doi:[10.1145/3158091](https://doi.org/10.1145/3158091); full version arXiv:1711.03363v1, <https://arxiv.org/abs/1711.03363v1>: Section 3.2, Definition 3.5, Proposition 3.6 with its proof and the paragraph after it, Definition 3.7, Remark 3.8, Definition 3.9, Section 4 (the three cases) and Definition 4.3.
