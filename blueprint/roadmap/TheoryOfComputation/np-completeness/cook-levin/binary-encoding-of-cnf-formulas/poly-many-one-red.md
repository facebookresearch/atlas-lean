# Polynomial-time many-one reduction

A decision problem $L_1$ reduces to a decision problem
$L_2$ in polynomial time when there is a polynomial-time computable function $f$ from lists of
Booleans to lists of Booleans such that $L_1(x) = L_2(f(x))$ for every list $x$ of Booleans.
