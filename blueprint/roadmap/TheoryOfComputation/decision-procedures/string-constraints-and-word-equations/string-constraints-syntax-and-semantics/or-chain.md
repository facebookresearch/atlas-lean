# Disjunction of a list of string formulas

Let $\alpha$ be an alphabet and $V$ a set of variables. For a finite list $\varphi_1, \dots, \varphi_k$ of string-constraint formulas over $\alpha$ with variables
in $V$, the disjunction chain is defined recursively as false for the empty list and as $\varphi_1 \vee
\psi$ otherwise, where $\psi$ is the disjunction chain of $\varphi_2, \dots, \varphi_k$. So it is
$\varphi_1 \vee (\varphi_2 \vee (\cdots (\varphi_k \vee \mathrm{false})))$.
