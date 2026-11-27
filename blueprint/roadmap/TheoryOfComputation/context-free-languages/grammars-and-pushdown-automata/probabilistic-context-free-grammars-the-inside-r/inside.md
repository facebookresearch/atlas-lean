# Inside recurrence

For a context-free grammar with rule weights $q$, the inside value $\beta_d(A, w)$ of a nonterminal $A$ on a string $w$ at depth bound $d$ is defined by $\beta_0 = 0$ and

$$\beta_{d+1}(A, w) = [w = a,\ A \to a \text{ a rule}]\, q(A \to a) + \sum_{A \to B\,C} \ \sum_{w = u v,\ u, v \ne \varepsilon} q(A \to B\,C)\, \beta_d(B, u)\, \beta_d(C, v),$$

where the first term is present only when $w$ is a single terminal $a$ and $A \to a$ is a rule of the grammar, and the sum runs over the binary rules of the grammar with left side $A$ and the splits of $w$ into two nonempty parts.
