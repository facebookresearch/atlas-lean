# Joint convexity of quantum relative entropy for singular and unnormalized matrices

Let $(\rho_k,\sigma_k)_{k\in K}$ be finitely many pairs of positive semidefinite matrices on $\mathbb{C}^\iota$ (possibly singular, not necessarily of trace one) and $w_k\ge 0$. Then

$$
D\Big(\sum_k w_k\rho_k\ \Big\|\ \sum_k w_k\sigma_k\Big) \le \sum_k w_k\, D(\rho_k\,\|\,\sigma_k),
$$

where $0\cdot(+\infty) = 0$, so a support mismatch at a positive weight makes the right side infinite.

## Proof sketch

If some positive-weight pair has a support mismatch the right side is infinite. Otherwise supports of the mixtures are compatible, and the integral representation writes both sides through the resolvent kernel minus a term linear in the trace. Joint convexity of the resolvent kernel at every parameter, integrated over $s \in [0,1]$, gives the claim.

## Depends on

- [Support inclusion and Umegaki relative entropy](umegaki-relative-entropy.md)
- [Joint convexity of the matrix relative entropy](../../../LinearAlgebra/positive-definite-matrices/matrix-relative-entropy/convex-on-relative-entropy.md)

## Proof depends on

- [Integral representation of relative entropy by the resolvent kernel](relative-entropy-resolvent-integral.md)
- [Joint convexity of the resolvent kernel](resolvent-kernel-joint-convexity.md)

## Sources

- M. B. Ruskai, "Another short and elementary proof of strong subadditivity of quantum entropy", Reports on Mathematical Physics 60(1):1-12, 2007.
- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
