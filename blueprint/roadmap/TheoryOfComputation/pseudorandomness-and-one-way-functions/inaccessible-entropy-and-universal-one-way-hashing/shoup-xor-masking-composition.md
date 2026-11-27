# Shoup's XOR-masking composition of target collision-resistant compression functions

Let $H_K : \{0,1\}^{b+s} \to \{0,1\}^{b}$ ($s \ge 1$) be a target collision-resistant compression family. For $t$ steps, with one key $K$ and $\lfloor \log_2 t \rfloor + 1$ public uniform $b$-bit masks $\kappa_0, \kappa_1, \dots$, define the cascade on inputs $(h_0, m_1, \dots, m_t)$ by

$$h_i = H_K\bigl((h_{i-1} \oplus \kappa_{\nu_2(i)}) \,\|\, m_i\bigr), \qquad i = 1, \dots, t,$$

where $\nu_2(i)$ is the 2-adic valuation of $i$. Then the cascade is a target collision-resistant family compressing $b + ts$ bits to $b$ bits with total key length $|K| + b(\lfloor\log_2 t\rfloor + 1)$; a cascade adversary with advantage $\varepsilon$ yields a step adversary with advantage at least $\varepsilon/t$.

## Proof sketch

A cascade collision on the committed target produces a collision at some step $i$. The reduction guesses $i$, receives a key, and reprograms the mask $\kappa_{\nu_2(i)}$ so that the target's chaining value at step $i$ matches its committed step target; the valuation pattern ensures that every other mask used before step $i$ can be chosen independently of the key.

## Depends on

- [Collision resistance and target collision resistance](../../../ComputerScience/cryptography/hash-functions/collision-resistance-and-target-collision-resistance.md)

## Sources

- V. Shoup, "A Composition Theorem for Universal One-Way Hash Functions", Advances in Cryptology (EUROCRYPT 2000), LNCS 1807, 2000.
- I. Haitner, T. Holenstein, O. Reingold, S. Vadhan and H. Wee, "Inaccessible Entropy II: IE Functions and Universal One-Way Hashing", Theory of Computing 16, 2020.
