# CSS codes

Calderbank and Shor build quantum error-correcting codes from two binary linear codes $C_2 \subseteq C_1 \subseteq \mathbb{F}_2^n$. For $w \in \mathbb{F}_2^n$ the codeword state is $|c_w\rangle = 2^{-\dim C_1/2} \sum_{v \in C_1} (-1)^{v \cdot w} |v\rangle$, it depends only on the coset $w + C_1^{\perp}$, and the code $Q_{C_1, C_2}$ is spanned by the $|c_w\rangle$ with $w \in C_2^{\perp}$; it encodes $\dim C_1 - \dim C_2$ qubits into $n$. Bit flips act inside the classical code $C_1$, while phase flips shift the index $w$ and become bit flips after a Hadamard change of basis, where they are corrected by $C_2^{\perp}$. If $C_1$ and $C_2^{\perp}$ both have minimum distance $d$, the code corrects $\lfloor (d-1)/2 \rfloor$ errors. With the $[7,4,3]$ Hamming code as $C_1$ and $C_2 = C_1^{\perp}$ this gives a code encoding one qubit into seven (Calderbank and Shor's example, Steane's code). Calderbank and Shor also show that such codes exist with asymptotic rate $1 - 2H_2(2t/n)$.

The error-correction theorem is stated through the [Knill–Laflamme notion of correctability](../knill-laflamme-conditions/README.md).

- [Sign of a binary digit](sign.md)
- [Binary vectors are their own negatives](add-self-eq-zero.md)
- [CSS codeword](codeword.md)
- [CSS codewords depend on $w$ modulo $C_1^{\perp}$](codeword-eq-of-add-mem-dual.md)
- [Character sums over a binary linear code](sum-sign-eq-zero.md)
- [Distinct CSS codewords are orthogonal](inner-codeword-eq-zero.md)
- [Norm of a CSS codeword](inner-codeword-self.md)
- [Pauli operator $X^a Z^b$ on $n$ qubits](pauli.md)
- [Action of a Pauli operator on a vector](pauli-mul-vec-apply.md)
- [A phase flip shifts the CSS codeword](pauli-zero-mul-vec-codeword.md)
- [A bit flip by a codeword of $C_1$ fixes the CSS codeword up to sign](pauli-mul-vec-codeword-of-mem.md)
- [CSS codes correct $\lfloor (d - 1) / 2 \rfloor$ errors](is-correctable-css.md)

## Related topics

- [Linear codes](../../../InformationTheory/error-correcting-codes/linear-codes/README.md): the classical codes $C_1$, $C_2$ and the dual code $C^{\perp}$ used in the construction.
- [Hamming (7,4) code](../../../InformationTheory/error-correcting-codes/hamming-7-4-code/README.md): the classical code behind Calderbank and Shor's seven-qubit example.
- [Knill–Laflamme conditions](../knill-laflamme-conditions/README.md): the correctability notion in which the error-correction theorem is stated.
- [Bounds on code size](../../../InformationTheory/error-correcting-codes/bounds-on-code-size/README.md): the classical Hamming, Singleton and Gilbert–Varshamov bounds that frame the parameters of $C_1$ and $C_2^{\perp}$.
