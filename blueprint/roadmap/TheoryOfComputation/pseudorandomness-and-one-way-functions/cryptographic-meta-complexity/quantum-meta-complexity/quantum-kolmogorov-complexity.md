# Quantum Kolmogorov complexity based on classical descriptions

Vitányi measures a pure state $|x\rangle$ by the shortest classical program that makes a quantum Turing machine output some state $|z\rangle$, plus the code length $\lceil-\log|\langle z|x\rangle|^{2}\rceil$ needed to redescribe $|x\rangle$ given $|z\rangle$.

Fix quantum Turing machines with one primitive rotation (cosine $3/5$, sine $4/5$) and a read-only, left-to-right program tape, so that halting programs form a prefix-free set. For a machine $Q$, a classical program $p$ and an auxiliary input $y$, $Q(p,y)$ is the pure state left on the output tape at halting, unentangled with the rest of the configuration. The (self-delimiting) complexity of a pure state $|x\rangle$ given $y$ is

$$
K_Q(|x\rangle\mid y)=\min_{p}\{\,l(p)+\lceil-\log|\langle z\mid x\rangle|^{2}\rceil : Q(p,y)=|z\rangle\,\},
$$

where $l(p)$ is the length of $p$; the minimizing $|z\rangle$ is the *directly computed part* and the logarithmic term the *approximation part*. **Invariance:** there is a universal machine $U$ such that for every $Q$ there is a constant $c_Q$ with $K_U(|x\rangle\mid y)\le K_Q(|x\rangle\mid y)+c_Q$ for all $|x\rangle$ and $y$. Fixing such a reference machine defines the quantum Kolmogorov complexity $K(|x\rangle\mid y)=K_U(|x\rangle\mid y)$ and $K(|x\rangle)=K_U(|x\rangle\mid\epsilon)$.

**Consistency:** if $|x\rangle$ is a vector of a directly computable orthonormal basis $\mathcal B$ given $y$, then $K(|x\rangle\mid y)$ equals $\min_p\{l(p):U(p,y)=|x\rangle\}$ up to an additive $K(\mathcal B\mid y)$; in particular, on classical objects quantum Kolmogorov complexity coincides with classical prefix complexity up to an additive constant.

## Expansion

The approximation part is the Shannon–Fano code length of $|x\rangle$ in a basis containing $|x\rangle$, given $|z\rangle$: measuring $|z\rangle$ in that basis yields $|x\rangle$ with probability $|\langle z|x\rangle|^{2}$. Keeping descriptions classical makes the count of descriptions countable, which is what gives invariance and the classical counting arguments; the price is that $K$ is not computable, though it can be approximated from above when the projection onto $|x\rangle$ can be measured repeatedly. Gács's alternative uses a universal semi-density matrix instead.

## Depends on

- [Kolmogorov complexity](../../../kolmogorov-complexity/k.md)

## Proof depends on

None.

## Sources

- Paul M. B. Vitányi, "Quantum Kolmogorov Complexity Based on Classical Descriptions", *IEEE Transactions on Information Theory*, 2001, https://doi.org/10.1109/18.945258; numbering from arXiv:quant-ph/0102108v2 (Definitions 1, 2 and 3, Theorem 1, Theorem 2, Corollary 1, Theorem 4).
