# Codes from small-bias lists have short correlation lists

Let $(r_z)_{z \in Z}$ be a $\delta$-biased list of vectors in $\{0,1\}^n$, and encode $x \in \{0,1\}^n$ as the word $z \mapsto \langle r_z, x\rangle$. Then the $\pm1$ word of every nonzero message has $\bigl|\sum_z (-1)^{\langle r_z, x\rangle}\bigr| \le \delta |Z|$, codewords of distinct messages have correlation at most $\delta|Z|$ in absolute value, and for every word $T : Z \to \{0,1\}$ and $\gamma, \delta \ge 0$ the number $N$ of messages $x$ with $\bigl|\sum_z (-1)^{T(z) + \langle r_z, x\rangle}\bigr| \ge \gamma|Z|$ satisfies $N(\gamma^2 - \delta) \le 1$.

## Proof sketch

The XOR of two codewords is the codeword of the nonzero sum message, which is $\delta$-balanced. For the list bound, the $\pm1$ codewords are unit vectors (after scaling by $|Z|^{-1/2}$) with pairwise inner products at most $\delta$; expanding $\|\sum_x \pm c_x\|^2 \ge (\sum_x |\langle T, c_x\rangle|)^2$ gives $N^2\gamma^2 \le N + N(N-1)\delta$.

## Depends on

- [Bias, ε-biased and k-wise ε-biased distributions](small-bias-distributions.md)

## Sources

- D. M. Kane and R. Williams, "Super-Linear Gate and Super-Quadratic Wire Lower Bounds for Depth-Two and Depth-Three Threshold Circuits", Proceedings of the 48th ACM Symposium on Theory of Computing, 2016.
