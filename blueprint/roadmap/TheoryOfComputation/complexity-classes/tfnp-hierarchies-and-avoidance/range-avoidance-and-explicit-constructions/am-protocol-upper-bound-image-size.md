# Ghentiyala–Li–Stephens-Davidowitz: an AM protocol upper-bounding the image size of a circuit

For every $\varepsilon=\varepsilon(n)\ge 1/\mathrm{poly}(n)$ there is an Arthur–Merlin protocol for the following promise problem. The input is a circuit $C\colon\{0,1\}^n\to\{0,1\}^m$ and an estimate $\tau\in[2^n]$. YES instances satisfy $|\mathrm{Im}(C)|\le\tau$; NO instances satisfy $|\mathrm{Im}(C)|\ge\tau+\varepsilon 2^n$. This complements the Goldwasser–Sipser set lower bound protocol, which certifies lower bounds on the size of $\mathrm{Im}(C)$ up to a multiplicative $1+1/\mathrm{poly}(n)$ factor; here Merlin certifies an upper bound up to additive error $\varepsilon 2^n$.

## Proof sketch

The protocol first approximates $|\mathrm{Im}(C)|$ through the identity $|\mathrm{Im}(C)|=\sum_{x\in\{0,1\}^n}1/|C^{-1}(C(x))|$, so an upper bound on the image follows from lower bounds on preimage sizes of random inputs. Merlin certifies these lower bounds with the Goldwasser–Sipser set lower bound protocol (based on pairwise independent hashing), and a Chernoff–Hoeffding bound over Arthur's random samples controls the additive error.

## Depends on

- [The class $\mathsf{AM}$ (Arthur–Merlin)](../../time-and-space-complexity-classes/am.md)

## Proof depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)
- [Goldwasser-Sipser: private coins add no power to interactive proofs](../../../randomized-and-quantum-complexity/goldwasser-sipser-theorem/goldwasser-sipser.md)

## Sources

- Surendra Ghentiyala, Zeyong Li and Noah Stephens-Davidowitz, "Range avoidance, Arthur-Merlin, and TFNP", ECCC TR25-210 (2025).
