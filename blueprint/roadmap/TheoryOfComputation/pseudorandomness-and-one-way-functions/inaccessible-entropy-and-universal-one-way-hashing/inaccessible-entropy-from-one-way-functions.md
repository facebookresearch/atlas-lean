# Inaccessible average max-entropy from any one-way function

Let $g$ be a one-way function with fixed output length $m(n)$. Define

$$F_0(x, A, b, r) = \bigl(A,\ b,\ r,\ \text{first } \min(r, n) \text{ bits of } A\,g(x) + b\bigr),$$

zero-padded to fixed length, where $A$ is a uniform $m(n) \times m(n)$ Boolean matrix, $b$ a uniform vector (a 3-wise independent affine hash), and $r$ a uniform index of $\lfloor \log_2 n\rfloor + 1$ bits. Then $F_0$ is polynomial-time computable and, for every constant $d > 0$, its accessible average max-entropy is eventually at most $H(Z \mid F_0(Z)) - d \log_2 n / n$, with $Z$ the uniform input; moreover the accessible sets can be chosen independently of the adversary.

## Proof sketch

When the prefix length is near $\log$ of the number of images "lighter" than $g(x)$, any collision finder that outputs a preimage outside a small light set yields an inverter for $g$ by guessing the hash prefix; hence efficient finders stay inside sets whose size is, on average, about $d\log n/n$ bits smaller than the real fiber.

## Depends on

- [Collision finders and accessible average max-entropy](accessible-average-max-entropy.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [Normalizing the output length of a one-way function](../one-way-function-transformations/normalizing-one-way-function-output-length.md)

## Sources

- I. Haitner, T. Holenstein, O. Reingold, S. Vadhan and H. Wee, "Inaccessible Entropy II: IE Functions and Universal One-Way Hashing", Theory of Computing 16, 2020.
