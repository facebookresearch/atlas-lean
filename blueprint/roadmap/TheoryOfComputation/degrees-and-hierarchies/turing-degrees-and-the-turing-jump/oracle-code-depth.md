# Depth of an oracle code

Oracle codes are built from the basic codes $\mathrm{zero}$, $\mathrm{succ}$, $\mathrm{left}$,
$\mathrm{right}$ and $\mathrm{oracle}$ by pairing, composition, primitive recursion and
minimization. Their depth is defined by recursion: every basic code has depth $0$, the depth of
$\mathrm{pair}(a, b)$, $\mathrm{comp}(a, b)$ and $\mathrm{prec}(a, b)$ is
$\max(\mathrm{depth}(a), \mathrm{depth}(b)) + 1$, and the depth of $\mathrm{rfind}(a)$ is
$\mathrm{depth}(a) + 1$.

## Sources

- H. Rogers Jr., *Theory of Recursive Functions and Effective Computability*, McGraw-Hill, 1967 (Gödel numberings; size bounds).
