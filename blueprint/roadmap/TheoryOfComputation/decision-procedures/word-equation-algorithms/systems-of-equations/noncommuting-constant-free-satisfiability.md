# Noncommuting satisfiability of constant-free equations is as hard as word equations

Satisfiability of systems of word equations with constants reduces in polynomial time to asking whether a constant-free system has a solution over a binary alphabet in which two given variables do not commute.

Let $\Sigma_2 = \{0, 1\}$. The noncommuting satisfiability problem of constant-free word equations asks: given a finite alphabet $\Xi$ of variables, a finite system $S$ of equations $(U, V)$ with nonempty sides $U, V \in \Xi^+$, and variables $x, y \in \Xi$, is there a morphism $\alpha : \Xi^* \to \Sigma_2^*$, possibly erasing, solving every equation of $S$ with $\alpha(xy) \neq \alpha(yx)$? For every $n \ge 1$, satisfiability of systems of word equations with nonempty sides and $n$ variables over a finite nonempty alphabet of constants reduces in polynomial time to this problem with $2n + 2$ variables, and without bounding the number of variables the general satisfiability problem reduces to it.

In particular the problem is NP-hard, and if it lies in NP, then so does satisfiability of word equations.

## Depends on

- [Solution of a word equation](../../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [A free submonoid that codes constants by two variables](free-submonoid-coding-constants.md)
- [Satisfiability of unary word-equation systems is NP-hard](../satisfiability/word-equation-satisfiability-is-np-hard.md)
- [NP-hardness transfers along reductions](../../../np-completeness/satisfiability/3-satisfiability/np-hard-of-poly-many-one-red.md)

## Expansion

Let $S$ be a system over variables $\Xi = \{x_1, \dots, x_n\}$ and constants $\Sigma_k = \{0, \dots, k - 1\}$. Introduce variables $a, b, y_1, \dots, y_n$, take the words $B$ and $C_i$ over $\{a, b\}$ of the free submonoid coding constants, replace each constant $i$ by $C_i$, and add the equations $x_i B y_i B = B y_i B x_i$; the given pair of variables is $a, b$. A solution $\alpha$ of $S$ gives the $\{a, b\}$-nonperiodic solution with $a \mapsto 0$, $b \mapsto 1$, $x_i \mapsto \tau(\sigma(\alpha(x_i)))$ and suitable values of $y_i$, where $\sigma(i) = C_i$ and $\tau$ renames $a, b$ to $0, 1$. Conversely, let $\beta$ be a solution with $\beta(ab) \neq \beta(ba)$, and let $M$ be the free monoid of words beginning and ending with $\beta(B)$, together with $\varepsilon$. Each added equation says that $\beta(x_i)$ commutes with $\beta(B y_i B) \in M \setminus \{\varepsilon\}$, so $\beta(x_i) \in M$. Since $M$ is free and the $\beta(C_i)$ lie in its basis, there are an alphabet $\Gamma \supseteq \Sigma_k$ and an injective morphism $\varphi : M \to \Gamma^*$ with $\varphi(\beta(C_i)) = i$. Let $\psi : \Gamma^* \to \Sigma_k^*$ fix $\Sigma_k$ and erase the other letters. Then $\alpha = \psi \circ \varphi \circ \beta \circ \sigma$ is defined, fixes every constant, and solves $S$, because $\beta(\sigma(U)) = \beta(\sigma(V))$ for each equation. NP-hardness follows already by applying this reduction to unary systems with nonempty sides. Adding a fresh variable $z$ and the tautological equation $z=z$ ensures $n \ge 1$ when necessary. For the conditional NP conclusion, compose the general reduction with an NP algorithm for the target problem; an equation with an empty side is first replaced by the equivalent equation $Uc = Vc$ for an existing constant $c$, making both sides nonempty.

## Sources

- Aleksi Saarela, "Hardness Results for Constant-Free Pattern Languages and Word Equations", ICALP 2020, LIPIcs 168, Article 140 (2020), https://doi.org/10.4230/LIPIcs.ICALP.2020.140, Lemma 15 and Theorem 16 with its proof (Section 5, "Noncommuting satisfiability"); Section 1 for the consequence on NP
