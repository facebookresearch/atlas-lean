# The decision problem $\mathrm{QSAT}_k$

For a natural number $k$, $\mathrm{QSAT}_k$ accepts
a bitstring $x$ exactly when $x$ decodes, under the standard bitstring encoding, to a pair
$(P, \varphi)$ of a quantifier prefix $P = (q_1, v_1), \dots, (q_n, v_n)$, where each $q_i$ is
$\exists$ (true) or $\forall$ (false) and each $v_i$ is a natural number, and a matrix circuit
$\varphi$, such that: $P$ is nonempty and $q_1$ is $\exists$; $(v_1, \dots, v_n)$ is a
permutation of $(0, \dots, n - 1)$; every variable of $\varphi$ is less than $n$; $\varphi$ is
well formed; $P$ has exactly $k$ quantifier blocks; and $(P, \varphi)$ is true under the
assignment that sends every variable to false. A bitstring that does not decode is rejected.
