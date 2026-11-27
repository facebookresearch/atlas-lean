# Hadamard tester for systems of quadratic equations

Let $q_1, \dots, q_m$ be quadratic polynomials over $\mathbb{F}_2$ in $u \in \mathbb{F}_2^n$. Consider proofs consisting of a table $f : \mathbb{F}_2^n \to \mathbb{F}_2$ (supposedly $x \mapsto \langle u, x\rangle$) and a table $g : \mathbb{F}_2^{n \times n} \to \mathbb{F}_2$ (supposedly $X \mapsto \langle u \otimes u, X\rangle$). The tester runs, each with constant probability: the BLR linearity test on $f$ and on $g$; the *tensor test*, which picks $x, y$ uniformly and checks $f(x) f(y) = g(x \otimes y)$ using self-corrected values; and the *equation test*, which picks a uniformly random subset of the equations and checks their sum using self-corrected values of $f$ and $g$. It makes $O(1)$ queries, accepts the honest tables of a solution with probability $1$, and there is an absolute constant $c > 0$ such that it rejects with probability at least $c/4$ if the system has no solution, and with probability at least $c\,\delta$ if $f$ is $\delta$-far from the Hadamard encodings of all solutions, for every $\delta \le 1/4$.

## Proof sketch

BLR soundness makes $f$ and $g$ close to linear functions with coefficient vectors $u$ and $B$. If $B \ne u \otimes u$ then the random bilinear test detects the nonzero matrix $B - u\otimes u$ with probability at least $1/4$. If $u$ violates some equation, a random subset sum of the equations is violated with probability $1/2$.

## Depends on

- [Blum–Luby–Rubinfeld linearity test](../blum-luby-rubinfeld-linearity-test/blr-test.md)
- [Relative Hamming distance on the Boolean cube](../blum-luby-rubinfeld-linearity-test/bool-dist.md)
- [Local decoding of the Hadamard code](../../../InformationTheory/error-correcting-codes/hadamard-code-local-decoding.md)

## Proof depends on

- [Acceptance probability of the BLR test in Fourier form](../blum-luby-rubinfeld-linearity-test/blr-accept-prob-eq.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- S. Arora, C. Lund, R. Motwani, M. Sudan and M. Szegedy, "Proof Verification and the Hardness of Approximation Problems", Journal of the ACM 45(3), 1998.
