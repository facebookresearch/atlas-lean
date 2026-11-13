# Nisan-Wigderson: exponential hardness in E derandomizes BPP

Suppose there are a decision
problem $f$ in E and a natural number $c > 0$ such that, for every $n$, every well-formed flat
Boolean circuit $C$ on $n$ inputs without mod gates that computes $f$ on all bitstrings of length
$n$ (for every bitstring $x$ of length $n$, the value of its last gate on input $x$ is $f(x)$)
satisfies $|C|^c \ge 2^n$, where $|C|$ is its number of gates; that is, $C$ has at least $2^{n/c}$
gates. Then BPP equals P.

## Sources

- N. Nisan and A. Wigderson, "Hardness vs randomness", Journal of Computer and System Sciences 49 (1994), 149-167 (FOCS 1988).
