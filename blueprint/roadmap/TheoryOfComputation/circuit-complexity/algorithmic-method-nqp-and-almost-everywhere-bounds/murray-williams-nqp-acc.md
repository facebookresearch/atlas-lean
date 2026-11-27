# Murray–Williams: NQP is not contained in ACC0

For every depth $d$ and modulus $m$, there is a language in $\mathrm{NQP} = \mathrm{NTIME}[n^{\operatorname{polylog}(n)}]$ that is not computed by any family of $\mathrm{AC}^0[m]$ circuits of depth $d$ and polynomial size. More strongly, $\mathrm{NTIME}[n^{\operatorname{polylog}(n)}] \not\subseteq \mathrm{ACC}^0 \circ \mathrm{THR}$ circuits of polynomial size, and $\mathrm{NQP}$ is not contained in $\mathrm{ACC}^0$ circuits of size $2^{\log^{k} n}$ for any fixed $k$.

## Proof sketch

Williams's $\mathrm{ACC}^0$-SAT algorithm runs in time $2^{n - n^{\delta}}$ for $\mathrm{ACC}^0$ circuits of size $2^{n^{\delta}}$, via the Yao/Beigel-Tarui transformation into symmetric functions of quasi-polynomially many $\mathrm{AND}$s and fast rectangular matrix multiplication. This is a non-trivial algorithm for subexponential size, so the algorithmic method template with the $\mathrm{NQP}$ easy witness lemma applies.

## Depends on

- [Nondeterministic quasi-polynomial time](nqp-class.md)
- [The class $\mathsf{ACC}^0$](../../complexity-classes/time-and-space-complexity-classes/acc0.md)

## Proof depends on

- [The algorithmic method template: non-trivial algorithms imply lower bounds](algorithmic-method-template.md)
- [Williams: NEXP is not contained in ACC0](../williams-nexp-not-in-acc0.md)

## Sources

- C. Murray, R. Williams, "Circuit lower bounds for nondeterministic quasi-polytime: an easy witness lemma for NP and NQP", STOC (2018); SIAM Journal on Computing 49 (2020).
- R. Williams, "Nonuniform ACC circuit lower bounds", Journal of the ACM 61 (2014).
- R. Williams, "New algorithms and lower bounds for circuits with linear threshold gates", STOC (2014); Theory of Computing 14 (2018).
