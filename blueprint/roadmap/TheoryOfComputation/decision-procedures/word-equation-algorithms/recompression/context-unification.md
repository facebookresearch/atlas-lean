# Context unification

Context unification asks whether an equation between first-order terms containing context variables, which stand for terms with exactly one hole, has a solution.

Fix a finite ranked signature $\Sigma$ that contains a constant, and let $\Omega \notin \Sigma$ be a constant standing for a hole. A ground context is a ground term over $\Sigma \cup \{\Omega\}$ with exactly one occurrence of $\Omega$; the ground context $\Omega$ is empty. For a ground context $s$ and a ground term or ground context $t$, $st$ denotes $s$ with its occurrence of $\Omega$ replaced by $t$; this composition is associative.

Let $\mathcal{V}$ be a set of first-order variables $x, y, \dots$ of arity $0$ and $\mathcal{C}$ a set of context variables $X, Y, \dots$ of arity $1$. Terms are the ground terms over $\Sigma \cup \mathcal{V} \cup \mathcal{C}$ with these arities, and a context equation is an equation $u = v$ between two terms. A substitution $\sigma$ assigns a ground term $\sigma(x)$ over $\Sigma$ to each $x \in \mathcal{V}$ and a ground context $\sigma(X)$ over $\Sigma$ to each $X \in \mathcal{C}$, and extends to terms by $\sigma(a) = a$ for constants $a \in \Sigma$, $\sigma(f(t_1, \dots, t_m)) = f(\sigma(t_1), \dots, \sigma(t_m))$ for $m$-ary $f \in \Sigma$, and $\sigma(X t) = \sigma(X)\, \sigma(t)$. It is a solution of $u = v$ if $\sigma(u) = \sigma(v)$; it is size-minimal if $|\sigma(u)| \le |\sigma'(u)|$ for every solution $\sigma'$, and nonempty if $\sigma(X) \neq \Omega$ for every context variable occurring in $u = v$.

Context unification is the decision problem: given $\Sigma$ and a context equation $u = v$, decide whether it has a solution.

## Depends on

None.

## Proof depends on

None.

## Expansion

When all non-constant symbols of $\Sigma$ are unary, a ground context is a chain $a_1 a_2 \cdots a_k \Omega$ of unary symbols, that is, a word $a_1 \cdots a_k$. For a fixed constant $c$, a word equation $U = V$ over the unary symbols, read with its variables as context variables and no first-order variables, becomes the context equation $U(c) = V(c)$, and its solutions correspond exactly to the solutions of $U = V$; in this sense context unification generalises word equations. It is also the special case of second-order unification in which a second-order variable uses its argument exactly once; second-order unification is undecidable. Context unification was introduced by H. Comon and, independently, by M. Schmidt-Schauß, and its decidability was a long-standing open problem of the rewriting community (RTA open problem 90). Restricting to nonempty solutions loses nothing: guess which context variables are empty and remove them.

## Sources

- Artur Jeż, "Context Unification is in PSPACE", ICALP 2014, LNCS 8573, 244–255 (2014), https://doi.org/10.1007/978-3-662-43951-7_21; read as arXiv:1310.4367v2, https://arxiv.org/abs/1310.4367v2, Definitions 1–3 (Section 3, "Context unification"), Section 1.1 for the relation to word equations and second-order unification, and the paragraph after Definition 3 for nonempty solutions
- Artur Jeż, "Solving Word Equations (And Other Unification Problems) by Recompression (Invited Talk)", CSL 2020, LIPIcs 152, Article 3 (2020), https://doi.org/10.4230/LIPIcs.CSL.2020.3, Section 3 ("Similar applications")
