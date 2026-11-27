# Breuckmann-Eberhardt: explicit balanced product codes

There is an explicit, non-random family of quantum LDPC codes, obtained as balanced products of Ramanujan-type Cayley graph complexes with classical Tanner codes, with parameters

$$
[[N,\ K,\ D]] \quad \text{where } K = \Theta(N^{4/5}), \ D = \Omega(N^{3/5}) .
$$

## Proof sketch

Take a balanced product over a group $G$ acting freely on an expander-based Tanner complex and on a cycle (or on a second Tanner complex). The homology of the balanced product is computed by a Künneth-type spectral sequence, giving the dimension. Distance lower bounds follow from expansion of the base graphs, through lifting logical cycles from the quotient complex, and balancing parameters yields the exponents $4/5$ and $3/5$.

## Depends on

- [Balanced products of chain complexes over a group](balanced-product-of-chain-complexes.md)
- [Quantum LDPC code families and asymptotically good quantum codes](quantum-ldpc-code-families-and-good-codes.md)

## Proof depends on

- [Parameters of hypergraph product codes](parameters-of-hypergraph-product-codes.md)

## Sources

- Nikolas P. Breuckmann, Jens N. Eberhardt, "Balanced product quantum codes", IEEE Transactions on Information Theory 67(10) (2021); arXiv:2012.09271.
