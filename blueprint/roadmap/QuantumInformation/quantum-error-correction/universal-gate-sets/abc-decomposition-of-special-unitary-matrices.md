# The $ABC$ decomposition of a special unitary matrix

For every $W \in SU(2)$ there are $A, B, C \in SU(2)$ with

$$A B C = I \qquad\text{and}\qquad A X B X C = W ,$$

where $X$ is the Pauli matrix $\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. Explicitly, if
$W = R_z(\alpha) R_y(\theta) R_z(\beta)$ ([Euler decomposition](euler-decomposition-of-single-qubit-unitaries.md)), one
may take $A = R_z(\alpha) R_y(\theta/2)$, $B = R_y(-\theta/2) R_z(-(\alpha + \beta)/2)$ and $C = R_z((\beta - \alpha)/2)$;
then $ABC = R_z(\alpha) R_z(-\alpha) = I$, and conjugating $B$ by $X$ flips the signs of its angles, which gives
$AXBXC = W$.

## Depends on

- [Euler decomposition of single-qubit unitaries](euler-decomposition-of-single-qubit-unitaries.md)

## Sources

- A. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo, N. Margolus, P. Shor, T. Sleator, J. Smolin and H. Weinfurter, *Elementary gates for quantum computation*, Phys. Rev. A 52 (1995), 3457–3467, arXiv:quant-ph/9503016, Section 4, Lemma 4.3 and its proof.
