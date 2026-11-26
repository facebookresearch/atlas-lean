# A homogeneous depth-five circuit for IMM of size n^{√n + 4}

Over every commutative semiring and for every $n\ge2$, $\mathrm{IMM}_{n,n}$ has a syntactically homogeneous $\Sigma\Pi\Sigma\Pi\Sigma$ circuit with at most $n^{\sqrt n+4}$ lower product, middle sum and upper product gates. Together with the lower bound, the homogeneous depth-five complexity of $\mathrm{IMM}_{n,n}$ over characteristic zero is $n^{\Theta(\sqrt n)}$.

## Proof sketch

Group the $n$ matrices into $r$ consecutive blocks of $t$ matrices ($rt\ge n$, $r\approx t\approx\sqrt n$). Each entry of a block product is a sum over $n^{t-1}$ paths of monomials (a $\Sigma\Pi$ expression), and the full product entry is a sum over $n^{r-1}$ choices of block boundary indices of products of $r$ block entries, giving $r\,n^{t+1}+rn^2+n^{r+1}$ gates.

## Depends on

- [Homogeneous depth-five (ΣΠΣΠΣ) circuits](homogeneous-depth-five-circuits.md)

## Sources

- OpenAI, "Homogeneous Depth-Five Lower Bounds for Iterated Matrix Multiplication", Preprint, 2026.
