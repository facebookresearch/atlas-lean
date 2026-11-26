# Natural property

Let $C = (C_n)_{n \in \mathbb{N}}$, where $C_n$ is a set of Boolean
functions on $n$ bits. Then $C$ is natural when it is constructive and large. Constructive: there
are a polynomial $q$ with natural-number coefficients and, for every $n$, a circuit given as a
list of at most $q(2^n)$ encoded gates, such that a Boolean function $g$ on $n$ bits lies in $C_n$
if and only if the evaluation of the circuit on the truth table of $g$ has last gate value true.
Large: there is a natural number $c$ such that $|C_n| \ge 2^{2^n} / 2^{cn}$ for every $n$, that is,
$C_n$ contains at least a $2^{-cn}$ fraction of the $2^{2^n}$ Boolean functions on $n$ bits.
