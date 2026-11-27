# Conjunction of a list of string formulas

Let $\alpha$ be an alphabet and $V$ a set of variables. For a finite list $\varphi_1, \dots, \varphi_k$ of string-constraint formulas over $\alpha$ with variables
in $V$, the conjunction chain is defined recursively as true for the empty list and as $\varphi_1 \wedge
\psi$ otherwise, where $\psi$ is the conjunction chain of $\varphi_2, \dots, \varphi_k$. So it is
$\varphi_1 \wedge (\varphi_2 \wedge (\cdots (\varphi_k \wedge \mathrm{true})))$.
