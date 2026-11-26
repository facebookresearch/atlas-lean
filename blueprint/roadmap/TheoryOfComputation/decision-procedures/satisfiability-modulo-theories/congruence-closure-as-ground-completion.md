# Congruence closure as ground completion

To decide a ground conjunction $u_1 \approx v_1 \wedge \dots \wedge u_n \approx v_n \wedge \neg s_1 \approx t_1 \wedge \dots \wedge \neg s_k \approx t_k$ with uninterpreted function symbols, first *flatten* the equations by naming every subterm with a fresh constant, obtaining *C-equations* $c_i \approx c_j$ between constants and *D-equations* $f(c_{i_1}, \dots, c_{i_n}) \approx c_{i_0}$. Writing $s \doteq t$ for $s \approx t$ or $t \approx s$, the inference rules on pairs $(E, R)$ of equations and ground rewrite rules are:

- **Simplify:** $E \cup \{c \doteq c'\}, R \cup \{c \to c''\} \vdash E \cup \{c'' \doteq c'\}, R \cup \{c \to c''\}$;
- **Delete:** $E \cup \{c \approx c\}, R \vdash E, R$;
- **Orient:** $E \cup \{c \doteq c'\}, R \vdash E, R \cup \{c \to c'\}$ if $c \succ c'$;
- **Collapse:** $E, R \cup \{t[c]_p \to c', c \to c''\} \vdash E, R \cup \{t[c'']_p \to c', c \to c''\}$ if $p \ne \varepsilon$;
- **Deduce:** $E, R \cup \{t \to c, t \to c'\} \vdash E \cup \{c \approx c'\}, R \cup \{t \to c\}$.

**Theorem.** Let $E_0$ be a finite set of C-equations, $R_0$ a finite set of D-equations oriented from left to right, and $\succ$ a total ordering on the constants. Then the inference system terminates in a final state $(E_m, R_m)$ with $E_m = \emptyset$, $R_m$ terminating and confluent, and $\approx_{E_0 \cup R_0}\ =\ \approx_{R_m}$. Flattening preserves $\approx$ between terms over the original symbols, so normalizing the $s_i$ and $t_i$ with $R_m$ decides the input conjunction, which gives a completion-based proof that congruence closure decides conjunctions of ground equalities.

## Depends on

- [Equational consequence and E-algebras](../../../Logic/first-order-logic/equational-logic/equational-consequence-and-e-algebras.md)
- [Confluence of a relation](../../../Logic/first-order-logic/term-rewriting/confluence-of-a-relation.md)

## Proof depends on

- [Convergent sets of equations decide their equational theory](../../../Logic/first-order-logic/equational-logic/convergent-equational-theories-are-decidable.md)

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 1.2, flattening, the inference rules and Theorem 1.1, pp. 4–5, and the discussion of flattening, pp. 6–7, presenting the Downey–Sethi–Tarjan algorithm after L. Bachmair and A. Tiwari, "Abstract congruence closure and specializations", CADE-17, LNCS 1831, 2000.
