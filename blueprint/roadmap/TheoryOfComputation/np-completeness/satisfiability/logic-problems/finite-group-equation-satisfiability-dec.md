# EQUATION SATISFIABILITY OVER A FINITE GROUP as a decision problem

Fix a group $G$ and a bijection $e$ from $\{0, \dots, n-1\}$ to $G$. The decision problem EQUATION SATISFIABILITY OVER A FINITE GROUP accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of token lists, to an instance that is [well-formed](well-formed-3.md) for $n$ and [feasible](finite-group-equation-satisfiability-fea.md) for $e$. It rejects every bitstring that does not decode to such an instance.
