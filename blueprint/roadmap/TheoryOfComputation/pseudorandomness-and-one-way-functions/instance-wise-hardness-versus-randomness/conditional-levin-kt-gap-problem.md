# Conditional Levin–Kolmogorov complexity Kt(x | z) and the gap problem GapMcKtP

Fix a universal machine $U$. The **conditional Levin–Kolmogorov complexity** of $x$ given auxiliary input $z$ is

$$
\mathrm{Kt}(x\mid z)=\min\{\,|\Pi|+\lceil\log t\rceil \;:\; U(\Pi,z)\text{ outputs }x\text{ within }t\text{ steps}\,\}.
$$

Given thresholds $T_{\mathrm{YES}}<T_{\mathrm{NO}}$, the promise problem $\mathrm{GapMcKtP}[T_{\mathrm{YES}},T_{\mathrm{NO}}]$ has YES instances the pairs $(x,z)$ with $|x|=|z|$ and $\mathrm{Kt}(x\mid z)\le T_{\mathrm{YES}}(|x|)$, and NO instances the pairs with $|x|=|z|$ and $\mathrm{Kt}(x\mid z)\ge T_{\mathrm{NO}}(|x|)$; pairs of intermediate complexity are outside the promise. The case of interest is $T_{\mathrm{YES}}=\gamma\log n$ for a constant $\gamma$ and $T_{\mathrm{NO}}=n-1$.

## Depends on

- [Kolmogorov complexity](../../kolmogorov-complexity/k.md)

## Sources

- Yanyi Liu and Rafael Pass, "Characterizing Derandomization Through Hardness of Levin-Kolmogorov Complexity", CCC (2022), ECCC TR22-084.
