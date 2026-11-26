# Oracle circuits and local circuit classes

An *oracle circuit* is a circuit that, besides Boolean gates, may contain *oracle gates* of arbitrary fan-in answering membership queries to a fixed language $\mathcal{O}$. For functions $q, \ell, a, s$ of the input length $N$, the class $[q, \ell, a]\text{-}\mathrm{Circuit}[s]$ consists of the languages computed by circuit families of size at most $s(N)$ with oracle gates to a single fixed oracle (the same for all lengths), each of fan-in at most $\ell(N)$, at most $q(N)$ oracle gates in total, and at most $a(N)$ oracle gates on any input-to-output path (adaptivity). An *oracle formula* is an oracle circuit whose Boolean gates are fan-in-two AND and OR gates with negations only at the inputs, and in which every gate, oracle gates included, has fan-out $1$. Such *local* classes capture the circuits produced by hardness magnification theorems.

## Depends on

- [Circuit complexity of a Boolean function and truth tables](../minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)

## Sources

- L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal and R. Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality", ITCS 2020.
