# Prediction success probability for the inner-product bit

For a list $C$ of serialized
gates and a map $\pi$ from $n$-bit strings to $n$-bit strings, the prediction success probability
of $C$ against $\pi$ is the rational number $N / 2^{2n}$, where $N$ is the number of pairs
$(x, r)$ of $n$-bit strings such that $C$ has at least one gate and the value of its last gate on
the concatenation of $\pi(x)$ and $r$, a $2n$-bit input, equals the inner product of $x$ and $r$
modulo 2.
