# Read-once oblivious algebraic branching programs

A *read-once oblivious algebraic branching program* (ROABP) of width $w$ in the variable order $x_{\pi(1)},\dots,x_{\pi(n)}$ computes an entry of a product $M_1(x_{\pi(1)})M_2(x_{\pi(2)})\cdots M_n(x_{\pi(n)})$ of $w\times w$ matrices whose entries in the $i$-th factor are univariate polynomials in $x_{\pi(i)}$ (of degree at most $\delta$). A polynomial is an *any-order ROABP* of width $w$ if it has such a representation in every order. The coefficient of a monomial in the product is the corresponding entry of the product of the coefficient matrices of the layers.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Sources

- Michael A. Forbes, Amir Shpilka, "Quasipolynomial-Time Identity Testing of Non-commutative and Read-Once Oblivious Algebraic Branching Programs", 54th Annual IEEE Symposium on Foundations of Computer Science (FOCS), 2013.
- Manindra Agrawal, Rohit Gurjar, Arpita Korwar, Nitin Saxena, "Hitting-Sets for ROABP and Sum of Set-Multilinear Circuits", SIAM Journal on Computing, 2015.
