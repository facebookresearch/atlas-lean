# Constraint subsampling preserves the Max-CSP optimum up to $2\delta m$

Let $F$ be a (weighted) Max-CSP instance with $m$ constraints on $n$ variables over a finite domain $D$. Draw $s$ constraints of $F$ uniformly and independently with replacement to obtain $F'$. If $s \ge 2\delta^{-2}(n \ln|D| + \ln(2/\eta))$, then with probability at least $1 - \eta$, simultaneously for all assignments $\sigma$, $|\tfrac{m}{s}\,\mathrm{score}_{F'}(\sigma) - \mathrm{score}_F(\sigma)| \le \delta m$; in particular an optimal assignment for $F'$ is within $2\delta m$ of the optimum of $F$.

## Proof sketch

For a fixed assignment the rescaled sampled score is an average of $s$ independent $[0,m]$-valued variables, so Hoeffding's inequality gives a tail $2e^{-2s\delta^2}$ for a deviation of $\delta m$; a union bound over the $|D|^n$ assignments finishes (already $s\ge\delta^{-2}(n\ln|D|+\ln(2/\eta))/2$ suffices, so the stated bound has slack), and the two one-sided deviations add to $2\delta m$ for the optimizer.

## Depends on

- [Maximum constraint satisfaction problems](maximum-constraint-satisfaction-problems.md)

## Sources

- N. Alon and J. H. Spencer, The Probabilistic Method, 4th ed., Wiley, 2016.
- M. Mitzenmacher and E. Upfal, Probability and Computing, 2nd ed., Cambridge University Press, 2017.
