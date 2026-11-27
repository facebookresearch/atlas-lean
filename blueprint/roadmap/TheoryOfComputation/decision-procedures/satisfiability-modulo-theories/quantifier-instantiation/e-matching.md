# E-matching

Let $E$ be a finite set of equations between ground terms, maintained with its congruence closure in an *E-graph* (see [congruence closure](../congruence-closure-decides-conjunctions-of.md)); $\mathrm{class}(t)$ is the congruence class of $t$ and $\mathrm{find}(t)$ its representative. A *pattern* is a non-ground term, and a substitution maps variables to ground terms. A substitution $\beta$ *E-matches* a pattern $p$ with a ground term $t$ if $E \models \beta(p) = t$. Quantifier instantiation by E-matching treats an instance $\beta(F)$ of a quantified formula $\forall \vec{x}\, F$ with pattern $p$ as relevant when $\beta(p)$ is represented in the E-graph. The abstract matching procedure computes sets of substitutions:

- $\mathrm{match}(x, t, S) = \{\beta \cup \{x \mapsto t\} \mid \beta \in S,\ x \notin \mathrm{dom}(\beta)\} \cup \{\beta \in S \mid x \in \mathrm{dom}(\beta),\ \mathrm{find}(\beta(x)) = \mathrm{find}(t)\}$;
- for a constant $c$, $\mathrm{match}(c, t, S) = S$ if $c \in \mathrm{class}(t)$ and $\emptyset$ otherwise;
- $\mathrm{match}(f(p_1, \dots, p_n), t, S) = \bigcup_{f(t_1, \dots, t_n) \in \mathrm{class}(t)} \mathrm{match}(p_n, t_n, \dots \mathrm{match}(p_1, t_1, S) \dots)$.

The procedure is sound and complete up to congruence: every $\beta \in \mathrm{match}(p, t, \{\emptyset\})$ E-matches $p$ with $t$, and conversely every substitution that E-matches $p$ with $t$ is congruent to one in $\mathrm{match}(p, t, \{\emptyset\})$. The procedure starts from $\{\emptyset\}$, the set holding the empty substitution: $\mathrm{match}$ only extends members of its third argument, so $\mathrm{match}(p, t, \emptyset) = \emptyset$. Deciding E-matching is NP-hard, and the number of matches can be exponential in the size of the E-graph.

## Depends on

- [Congruence closure decides conjunctions of ground equalities](../congruence-closure-decides-conjunctions-of.md)

## Sources

- L. de Moura and N. Bjørner, "Efficient E-matching for SMT solvers", in *Automated Deduction (CADE-21)*, LNCS 4603, Springer, 2007, pp. 183–198, <https://leodemoura.github.io/files/ematching.pdf>, Section 2 (patterns, substitutions, congruence closure and E-graphs) and Section 2.1 (E-matching for quantifier instantiation, the abstract algorithm of Figure 1 and its soundness and completeness claim, justified in the work cited there; the source starts the procedure from $\emptyset$, and the start from $\{\emptyset\}$ is written out here), and Section 1 (NP-hardness and the number of matches).
