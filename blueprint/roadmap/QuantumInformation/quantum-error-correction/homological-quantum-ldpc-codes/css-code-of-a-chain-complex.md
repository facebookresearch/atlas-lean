# The CSS code of a chain complex

The *CSS code* of a chain complex $C_2 \xrightarrow{\partial_2} C_1 \xrightarrow{\partial_1} C_0$ has $n = \dim C_1$ physical qubits, $X$-check matrix $H_X = \partial_2^{T}$ and $Z$-check matrix $H_Z = \partial_1$; the condition $H_X H_Z^{T} = (\partial_1 \partial_2)^{T} = 0$ is the CSS commutation condition. Its parameters $[[n, k, d]]$ are

$$
k = \dim H_1, \quad d_Z = \min\{|c| : c \in \ker\partial_1 \setminus \mathrm{im}\,\partial_2\}, \quad d_X = \min\{|c| : c \in \ker\partial_2^{T} \setminus \mathrm{im}\,\partial_1^{T}\}, \quad d = \min(d_X, d_Z).
$$

## Depends on

- [Binary chain complexes of length two and their homology](binary-chain-complexes-of-length-two.md)
- [CSS codeword](../css-codes/codeword.md)
- [Stabilizer codes: correctability criterion and distance](../stabilizer-codes-correctability-criterion-and-distance.md)
- [Distance of a quantum code (lower bound)](../distance-of-a-quantum-code/has-distance-at-least.md)

## Sources

- A. R. Calderbank, Peter W. Shor, "Good quantum error-correcting codes exist", Physical Review A 54 (1996); arXiv:quant-ph/9512032.
- Jean-Pierre Tillich, Gilles Zemor, "Quantum LDPC codes with positive rate and minimum distance proportional to the square root of the blocklength", IEEE Transactions on Information Theory 60(2) (2014); arXiv:0903.0566.
