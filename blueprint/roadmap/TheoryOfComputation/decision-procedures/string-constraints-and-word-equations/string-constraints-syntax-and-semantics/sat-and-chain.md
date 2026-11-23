# Satisfaction of a conjunction chain

Let $\alpha$ be an alphabet and $V$ a set of variables. For a finite list $\varphi_1, \dots, \varphi_k$ of formulas, the conjunction chain is $\varphi_1 \wedge (\varphi_2 \wedge (\cdots (\varphi_k \wedge \mathrm{true})))$ and the disjunction chain is $\varphi_1 \vee (\varphi_2 \vee (\cdots (\varphi_k \vee \mathrm{false})))$. An assignment satisfies an atom formula as above, a conjunction if it satisfies both parts, a disjunction if it satisfies at least one part, always satisfies true and never satisfies false. For every assignment $\sigma : V \to \alpha^*$ and every finite list of string-constraint formulas,
$\sigma$ satisfies the conjunction chain of the list if and only if $\sigma$ satisfies every formula of the
list (in particular, every assignment satisfies the chain of the empty list).
