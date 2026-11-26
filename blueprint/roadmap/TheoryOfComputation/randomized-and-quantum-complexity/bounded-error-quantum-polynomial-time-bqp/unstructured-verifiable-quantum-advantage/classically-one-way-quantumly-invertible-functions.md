# Functions that are classically one-way but quantumly invertible relative to a random oracle

Relative to a random oracle, there exist functions that are collision resistant (hence one-way) against classical polynomial-time adversaries yet can be inverted by quantum polynomial-time algorithms; analogous separations hold for digital signatures and, assuming a classically CPA-secure encryption scheme, for public-key encryption.

## Proof sketch

For the Yamakawa–Zhandry code $C$, define $f^H_C:C\to\{0,1\}^n$ by $f^H_C(c_1,\dots,c_n)=(H_1(c_1),\dots,H_n(c_n))$. Inverting $f^H_C$ at $y$ means finding a codeword $c$ with $H_i(c_i)=y_i$ for all $i$, a codeword search problem; the classical query lower bound for every fixed target $y$, together with the fact that $f^H_C(x)$ for uniform $x\in C$ is almost independent of $H$, gives one-wayness. The quantum sampler, run with targets $y_i$ in place of $1$, outputs a near-uniform preimage of any $y$. Collision resistance against classical adversaries uses a modified, compressing version of the construction.

## Depends on

- [Search problems relative to a random oracle](search-problems-relative-to-a-random-oracle.md)

## Proof depends on

- [Yamakawa-Zhandry: unconditional NP search separation relative to a random oracle](np-search-separation-relative-to-a-random-oracle.md)

## Sources

- Takashi Yamakawa, Mark Zhandry, "Verifiable quantum advantage without structure", FOCS (2022), Journal of the ACM 71(3) (2024); arXiv:2204.02063.
