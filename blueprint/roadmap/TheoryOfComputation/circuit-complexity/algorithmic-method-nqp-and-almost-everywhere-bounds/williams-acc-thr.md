# Williams: NEXP is not computed by ACC0 circuits with a layer of threshold gates

For every $d, m$ there is $\varepsilon > 0$ such that $\mathrm{NEXP}$ is not contained in the class of $\mathrm{ACC}^0 \circ \mathrm{THR}$ circuits of depth $d$, modulus $m$ and size $2^{n^{\varepsilon}}$, i.e. $\mathrm{AC}^0[m]$ circuits whose bottom layer consists of arbitrary linear threshold gates. The underlying algorithm counts satisfying assignments of such circuits with $n^{2 - \varepsilon'}$ threshold gates in time $2^{n - n^{\varepsilon'}}$.

## Proof sketch

Each linear threshold gate on $n$ inputs is equivalent, over a domain partitioned by a small number of hyperplane arrangements, to a sum of exact-threshold gates with polynomially bounded weights; these combine with the $\mathrm{ACC}^0$ part into symmetric functions of quasi-polynomially many conjunctions of exact thresholds. Evaluating all of them on all inputs reduces to rectangular matrix multiplication, giving a non-trivial counting algorithm and hence the lower bound by the algorithmic method.

## Depends on

- [The algorithmic method template: non-trivial algorithms imply lower bounds](algorithmic-method-template.md)

## Proof depends on

- [The algorithmic method template: non-trivial algorithms imply lower bounds](algorithmic-method-template.md)

## Sources

- R. Williams, "New algorithms and lower bounds for circuits with linear threshold gates", STOC (2014); Theory of Computing 14 (2018).
