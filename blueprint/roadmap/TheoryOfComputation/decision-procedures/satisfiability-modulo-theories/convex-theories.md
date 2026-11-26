# Convex theories

A first-order theory $T$ over a signature $\Sigma$ is *convex with respect to equations* if for every conjunction $\Gamma$ of $\Sigma$-equations and non-equational $\Sigma$-literals and all $\Sigma$-equations $A_1, \dots, A_n$: whenever $T \models \forall \vec x\,(\Gamma \to A_1 \vee \dots \vee A_n)$, then $T \models \forall \vec x\,(\Gamma \to A_j)$ for some $j$. It suffices to require this for equations $A_i$ between variables. A theory has a *trivial model* if it has a model with exactly one element. $T$ is *stably infinite* if every formula $\exists \vec x\, F$ with $F$ quantifier-free that has a model of $T$ has a model of $T$ with a countably infinite universe; this is the notion used in [Nelson–Oppen combination](nelsonoppen-combination-of-decision-procedures.md).

## Depends on

- [Nelson–Oppen combination of decision procedures](nelsonoppen-combination-of-decision-procedures.md)

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 1.11, stably infinite theories, p. 24, convexity, p. 28, and Lemma 1.12, p. 31.
