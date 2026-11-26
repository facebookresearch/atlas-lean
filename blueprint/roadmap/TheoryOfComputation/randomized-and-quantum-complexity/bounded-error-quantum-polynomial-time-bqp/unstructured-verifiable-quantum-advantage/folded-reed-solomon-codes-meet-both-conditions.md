# Folded Reed-Solomon codes satisfy the dual-decodability and list-recovery conditions

For constant folding parameter $s$, rate $R \in (1/s, 1 - 1/s)$, and polynomial alphabet size $q = \mathrm{poly}(n)$ matching the Yamakawa–Zhandry parameter regime, folded Reed–Solomon codes satisfy simultaneously: (i) the dual code is efficiently decodable from the coordinatewise-independent error distribution required by the quantum algorithm (its dual is again an evaluation-type code decodable beyond half the distance for random errors), and (ii) the code is list recoverable with the parameters required by the classical lower bound.

## Proof sketch

The dual of a (folded) Reed-Solomon code is a generalized (folded) Reed-Solomon code, decodable from random errors of rate close to its relative distance using list decoding up to capacity followed by uniqueness for random errors. List recoverability of folded Reed-Solomon codes up to capacity with polynomial list size is due to Guruswami and Rudra; parameters are chosen so that rates of the two codes are compatible.

## Depends on

- [Quantum algorithm for codeword search via dual decoding](regev-style-quantum-sampling-of-oracle-good-codewords.md)
- [Classical query lower bound from list recoverability](classical-hardness-from-list-recovery.md)

## Proof depends on

- [Quantum algorithm for codeword search via dual decoding](regev-style-quantum-sampling-of-oracle-good-codewords.md)
- [Classical query lower bound from list recoverability](classical-hardness-from-list-recovery.md)

## Sources

- Takashi Yamakawa, Mark Zhandry, "Verifiable quantum advantage without structure", FOCS (2022), Journal of the ACM 71(3) (2024); arXiv:2204.02063.
