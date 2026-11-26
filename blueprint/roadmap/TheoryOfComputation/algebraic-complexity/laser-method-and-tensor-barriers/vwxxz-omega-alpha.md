# Vassilevska Williams–Xu–Xu–Zhou: omega <= 2.371552 and alpha >= 0.321334

A further variant of the asymmetric laser method, which applies the asymmetric hashing at every level and handles rectangular target shapes, gives

$$
\omega \le 2.371552, \qquad \alpha \ge 0.321334,
$$

where $\alpha$ is the dual matrix multiplication exponent, the largest $a$ with $\omega(1, a, 1) = 2$. Similar improvements hold for all rectangular exponents $\omega(1, k, 1)$. A subsequent analysis with more asymmetry (Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou) gives $\omega < 2.371339$.

## Proof sketch

Extend asymmetric hashing so that each level can choose which of the three sides is hashed, set up a sequence of optimization programs for rectangular values of constituents, and solve them for $\mathrm{CW}_q^{\otimes 16}$ and rectangular targets.

## Depends on

- [Dual matrix multiplication exponent](../matrix-multiplication-exponent/dual-matrix-multiplication-exponent.md)

## Proof depends on

- [Duan–Wu–Zhou: omega < 2.371866, breaking the Coppersmith–Winograd barrier](dwz-omega.md)
- [Vassilevska Williams–Xu–Xu–Zhou upper bound for matrix multiplication](../matrix-multiplication-exponent/vassilevska-williams-xu-xu-zhou2023-uppe.md)
- [Alman–Duan–Vassilevska Williams–Xu–Xu–Zhou upper bound for matrix multiplication](../matrix-multiplication-exponent/alman-duan-vassilevska-williams-xu-xu-zh.md)

## Sources

- V. Vassilevska Williams, Y. Xu, Z. Xu, R. Zhou, "New bounds for matrix multiplication: from alpha to omega", SODA (2024), arXiv:2307.07970.
- J. Alman, R. Duan, V. Vassilevska Williams, Y. Xu, Z. Xu, R. Zhou, "More asymmetry yields faster matrix multiplication", SODA (2025), arXiv:2404.16349.
