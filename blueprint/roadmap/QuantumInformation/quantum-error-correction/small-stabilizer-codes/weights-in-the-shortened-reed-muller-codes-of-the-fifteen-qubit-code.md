# Weights in the shortened Reed–Muller codes of the fifteen-qubit code

Let $L_1 \subseteq L_2 \subseteq \mathbb{F}_2^{15}$ be the shortened first- and second-order Reed–Muller codes: $[f]$ is the table of values of
$f : \mathbb{F}_2^4 \to \mathbb{F}_2$ at the fifteen nonzero points, $L_1$ is spanned by $[x_1], \dots, [x_4]$ and $L_2$ by
these and the six $[x_i x_j]$. Write $|u|$ for the Hamming weight, $u \cdot v$ for the coordinatewise product and $[1]$ for
the all-ones word. Then

1. $|u| \equiv 0 \pmod 8$ for every $u \in L_1$;
2. $|v| \equiv 0 \pmod 2$ for every $v \in L_2$;
3. $L_1^{\perp} = L_2 \oplus \langle [1] \rangle$ and $L_2^{\perp} = L_1 \oplus \langle [1] \rangle$;
4. $|u \cdot v| \equiv 0 \pmod 4$ for all $u, v \in L_1$;
5. $|u \cdot v| \equiv 0 \pmod 4$ for all $u \in L_1$ and $v \in L_2^{\perp}$.

Proof: a nonzero linear function takes the value $1$ at exactly eight points, and the generators $[x_i x_j]$ have weight
$4$; the basis vectors of $L_1$ and $L_2$ are orthogonal and the dimensions $4$ and $10$ give part 3; for independent
linear $f, g$ a change of coordinates makes $|[f] \cdot [g]| = |[y_1 y_2]| = 4$, and part 5 follows from
$|u \cdot ([1] + w)| = |u| - |u \cdot w|$.

## Depends on

- [Linear code](../../../InformationTheory/error-correcting-codes/linear-codes/linear-code.md)
- [Dual code](../../../InformationTheory/error-correcting-codes/linear-codes/dual.md)

## Proof depends on

- [Dimension and distance of binary Reed–Muller codes](../../../InformationTheory/error-correcting-codes/reed-muller-codes-dimension-and-distance.md)

## Related topics

- [The fifteen-qubit quantum Reed–Muller code](fifteen-qubit-quantum-reed-muller-code.md): the quantum code built from these two codes

## Sources

- S. Bravyi and A. Kitaev, *Universal quantum computation with ideal Clifford gates and noisy ancillas*, Phys. Rev. A 71 (2005), 022316, arXiv:quant-ph/0403025, Section VI, the definition of $L_1$, $L_2$ (equation (26)) and Lemma 1 with its proof.
