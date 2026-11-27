# Kane–Williams random restriction lemmas for linear threshold functions

Let $f$ be a linear threshold function on $n$ variables, let $P$ be a partition of $\{1,\dots,n\}$ into parts of equal size, and let $\rho\sim R_P$ be the random restriction that leaves one uniformly random variable of each part alive and fixes all other variables to independent uniform bits (so about $|P|$ variables stay alive). Then (gate version)

$$
\Pr_{\rho\sim R_P}[f|_\rho\text{ is not constant}]=O\bigl(|P|/\sqrt n\bigr),
$$

and (wire version) if $f$ depends on only $w$ of its inputs, then $f|_\rho$ fails to be a constant or a function of a single variable with probability $O\bigl(w|P|^{3/2}/n^{3/2}\bigr)$. As a consequence, every function agreeing with Andreev's function $A_n$ on a $\tfrac12+\varepsilon$ fraction of the $n$-bit inputs, for $\varepsilon\gg\sqrt{\log(n)/n}$, needs depth-two weighted threshold circuits with $\Omega(\varepsilon^3n^{3/2}/\log^3n)$ gates and $\Omega(\varepsilon^3n^{5/2}/\log^{7/2}n)$ wires; in particular computing $A_n$ exactly needs $\Omega(n^{3/2}/\log^3 n)$ gates and $\Omega(n^{5/2}/\log^{7/2}n)$ wires.

## Proof sketch

A threshold function $[\sum_ia_ix_i\ge t]$ is not forced to a constant exactly when the partial sum over the fixed variables falls in an interval determined by the alive weights; the Littlewood–Offord lemma bounds the probability of this event for a random assignment, which gives both versions. For Andreev's function, take the partition of the parity blocks of $A_n$, so that $\rho$ leaves one alive variable per block and $A_n|_\rho$ becomes, up to negations, the multiplexer applied to a fixed hard truth table on $k=O(\log n)$ alive inputs. By the two lemmas some $\rho$ fixes all but few bottom gates to constants or single wires, so a small circuit would leave a small depth-two threshold circuit approximating that truth table, while counting the functions computed by such circuits shows that a suitable truth table has no such approximation.

## Depends on

- [Depth-two weighted threshold circuits](depth-two-weighted-threshold-circuits.md)
- [Andreev's function](../../circuit-models-synthesis-and-lower-bounds/lower-bounds-for-general-circuits-and-formulas/formula-size-lower-bounds/andreev-function.md)

## Proof depends on

- [Counting threshold functions over a feature family](counting-threshold-functions.md)

## Sources

- Daniel M. Kane, Ryan Williams, "Super-Linear Gate and Super-Quadratic Wire Lower Bounds for Depth-Two and Depth-Three Threshold Circuits", Proceedings of the Forty-Eighth Annual ACM Symposium on Theory of Computing (STOC 2016), 2016 (Lemma 1.1, Lemma 3.1 and Theorem 1.1).
