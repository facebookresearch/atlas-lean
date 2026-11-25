# Polynomial-time verifier for dense CNF-SAT

The verifier machine computes, in polynomial
time, the map sending a pair $(w, y)$ of bit lists to the Boolean $\mathrm{check}(w, y)$, which
is true exactly when $y$ satisfies the CNF formula decoded from $w$. The pair is given as the
input $w \# y$ (the bits of $w$, a separator $\#$, then the bits of $y$), the output is the
single bit $\mathrm{check}(w, y)$, and the machine halts within $2(n + 5)^2$ steps on an input
of length $n$.
