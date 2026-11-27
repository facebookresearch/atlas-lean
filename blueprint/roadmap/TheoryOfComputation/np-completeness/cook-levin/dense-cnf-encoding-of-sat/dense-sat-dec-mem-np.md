# Dense CNF-SAT is in NP

The [dense CNF-SAT decision problem](dense-sat-dec.md) is in NP: there are a polynomial $p$ with natural-number
coefficients and a Boolean function $R$ on pairs of bit strings, computable in polynomial time (with pairs given by
their canonical bit-string code), such that for every bit string $w$, the formula decoded from $w$ in the dense
clause encoding is satisfiable if and only if $R(w, y)$ is true for some bit string $y$ with $|y| \le p(|w|)$.
