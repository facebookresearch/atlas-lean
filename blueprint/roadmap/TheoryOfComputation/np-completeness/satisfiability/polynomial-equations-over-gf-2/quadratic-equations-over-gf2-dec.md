# QUADRATIC EQUATIONS OVER GF[2] as a decision problem

The decision problem QUADRATIC EQUATIONS OVER GF[2] accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs $(n, \mathcal{P})$ (a natural number and a list of lists of lists of natural numbers), to an instance that is well-formed for QUADRATIC EQUATIONS OVER GF[2] and feasible for ALGEBRAIC EQUATIONS OVER GF[2] (a common zero in $\mathrm{GF}(2)^n$). It rejects every bitstring that does not decode to such an instance.
