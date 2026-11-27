# A symmetric binary matrix plus a diagonal is a Gram matrix

For every symmetric matrix $A \in \mathbb{F}_2^{n \times n}$ there are a diagonal matrix $\Lambda$ and an invertible
matrix $M \in \mathbb{F}_2^{n \times n}$ with $A + \Lambda = M M^{T}$. One can take $M$ lower triangular with ones on the
diagonal: the equations $A_{ij} = \sum_{k} M_{ik} M_{jk}$ for $i > j$ read
$A_{ij} = \sum_{k < j} M_{ik} M_{jk} + M_{ij}$, which determine the entries $M_{ij}$ one by one in order of $(i, j)$, and
$\Lambda$ is then chosen so that the diagonal equations hold.

## Sources

- S. Aaronson and D. Gottesman, *Improved simulation of stabilizer circuits*, Phys. Rev. A 70 (2004), 052328, arXiv:quant-ph/0406196, Section VI, Lemma 7 and its proof.
