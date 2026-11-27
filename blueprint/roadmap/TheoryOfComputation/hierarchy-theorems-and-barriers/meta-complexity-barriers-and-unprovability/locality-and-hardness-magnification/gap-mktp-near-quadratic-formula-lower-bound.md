# Gap-MKtP requires near-quadratic De Morgan formulas

In the small-threshold regime needed for magnification, the gap version of MKtP already requires De Morgan formulas of size $N^{2-\alpha}$ for every $\alpha \in (0,2)$, close to the cubic magnification threshold for such formulas.

For every constant $0 < \alpha < 2$ there is $C > 1$ such that

$$
\mathrm{Gap\text{-}MKtP}\big[C n^2,\ 2^{(\alpha/2) n - 2}\big] \notin U_2\text{-}\mathsf{Formula}[N^{2-\alpha}],
$$

where $N = 2^n$ is the input length, the yes-instances are the strings of Kt complexity at most $C n^2$, the no-instances are those of Kt complexity greater than $2^{(\alpha/2)n - 2}$, and formula size counts leaves. The constant $C$ depends exponentially on $1/\alpha$.

## Expansion

The proof adapts the Hirahara–Santhanam lower bound for MCSP. A formula of sub-quadratic size shrinks under a pseudorandom restriction, generated from few random bits and still shrinking formulas, so the restricted formula depends on few of the remaining free variables. Because the restriction has a short description, it can be completed both to a string of Kt complexity at most $C n^2$ and to a string of Kt complexity above $2^{(\alpha/2)n-2}$ that the simplified formula cannot distinguish; composing several such restrictions lowers the yes-threshold to $C n^2$.

## Depends on

- [The minimum Kt problem MKtP](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/the-minimum-kt-problem.md)
- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Proof depends on

None.

## Sources

- Igor C. Oliveira, Ján Pich and Rahul Santhanam, "Hardness Magnification Near State-of-the-Art Lower Bounds", *Theory of Computing* 17(11), 2021 (CCC 2019 special issue), DOI 10.4086/toc.2021.v017a011 (Theorem 1.3 and its footnote on the constant C; proof in Section 5.1).
