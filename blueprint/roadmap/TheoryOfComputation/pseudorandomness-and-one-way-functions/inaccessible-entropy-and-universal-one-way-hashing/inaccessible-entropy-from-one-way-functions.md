# Inaccessible average max-entropy from any one-way function

Let $f : \{0,1\}^n \to \{0,1\}^n$ be a length-preserving one-way function (any one-way function yields one by normalizing its output length), and let $\mathcal{G}$ be a family of hash functions $g : \{0,1\}^n \to \{0,1\}^n$ that is three-wise independent and constructible (members can be evaluated in polynomial time, and for any $x, y \in \{0,1\}^n$ a uniformly random member $g \in \mathcal{G}$ with $g(x) = y$ can be sampled in probabilistic polynomial time; Haitner–Holenstein–Reingold–Vadhan–Wee, Section 2). Define $F$ on $\mathrm{Dom}(F) = \{0,1\}^n \times \mathcal{G} \times [n]$ by

$$F(x, g, i) = \bigl(g(f(x))_{1..i},\ g,\ i\bigr),$$

where $g(f(x))_{1..i}$ is the first $i$ bits of $g(f(x))$. Then $F$ is polynomial-time computable and, for every constant $d > 0$, its accessible average max-entropy is at most $H(Z \mid F(Z)) - d \log_2 n / n$, with $Z$ uniform on $\mathrm{Dom}(F)$ (Haitner–Holenstein–Reingold–Vadhan–Wee, Theorem 4.5); moreover the accessible sets can be chosen independently of the adversary.

## Proof sketch

For a large constant $c$, the accessible set of $(x, g, i)$ consists of the inputs $(x', g, i)$ with $g(f(x'))_{1..i} = g(f(x))_{1..i}$ whose image $f(x')$ is $f(x)$ itself or *$i$-light*, $|f^{-1}(f(x'))| \le 2^{n-i}/n^c$. A collision finder that leaves these sets with noticeable probability yields an inverter for $f$ (Claim 4.6), and the sets are on average $\Omega(c \log n / n)$ bits smaller than the fibers of $F$ (Claim 4.7).

## Depends on

- [Collision finders and accessible average max-entropy](accessible-average-max-entropy.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [Normalizing the output length of a one-way function](../one-way-function-transformations/normalizing-one-way-function-output-length.md)

## Sources

- I. Haitner, T. Holenstein, O. Reingold, S. Vadhan and H. Wee, "Inaccessible Entropy II: IE Functions and Universal One-Way Hashing", Theory of Computing 16(8), 2020: Theorem 4.5, with the accessible sets (4.4)-(4.5) and Claims 4.6-4.7.
