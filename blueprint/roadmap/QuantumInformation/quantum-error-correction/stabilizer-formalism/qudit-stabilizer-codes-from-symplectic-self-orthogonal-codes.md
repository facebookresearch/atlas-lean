# Qudit stabilizer codes correspond to symplectic self-orthogonal additive codes

Let $q$ be a prime power. A stabilizer code over $\mathbb{F}_q$ is the joint fixed space of an abelian subgroup $S$ of the
[qudit error group](qudit-pauli-operators-over-a-finite-field.md) $G_n$ meeting the scalars only in $I$; for $K > 1$ it is an
$((n, K, d))_q$ code if it has dimension $K$ and detects every error of weight less than $d$ but not every error of weight $d$ (the weight of
$\omega^c X(\mathbf a) Z(\mathbf b)$ being the number of positions $i$ with $(a_i, b_i) \ne (0, 0)$, the symplectic weight
$\operatorname{swt}$). For $K = 1$ detection gives no distance, since every operator acts on a one-dimensional code as a
scalar; there $d$ is the least weight of an element of $S$ other than $I$, the convention of Ketkar et al. under which
a one-dimensional code is pure. An $((n, K, d))_q$ stabilizer code exists if and only if there is an additive code
$C \le \mathbb{F}_q^{2n}$ with $|C| = q^n / K$ and $C \le C^{\perp_s}$, the trace-symplectic dual, such that
$\operatorname{swt}(C^{\perp_s} \setminus C) = d$ when $K > 1$, and $\operatorname{swt}(C^{\perp_s} \setminus \{0\}) = d$ with
$C = C^{\perp_s}$ when $K = 1$.
Here $C$ is the image of $S$ modulo scalars and $C^{\perp_s}$ that of its centralizer. For $q = 2$ this is the
correspondence between stabilizer codes and symplectic self-orthogonal binary codes.

## Depends on

- [Qudit Pauli operators over a finite field](qudit-pauli-operators-over-a-finite-field.md)

## Proof depends on

- [Qudit Pauli operators over a finite field](qudit-pauli-operators-over-a-finite-field.md)

## Sources

- A. Ketkar, A. Klappenecker, S. Kumar and P. K. Sarvepalli, *Nonbinary stabilizer codes over finite fields*, IEEE Trans. Inform. Theory 52 (2006), 4892–4914, arXiv:quant-ph/0508070, Section III, Lemmas 7–11 and Theorem 13 with its proof.
