# Threshold and majority are in NC1

For all $k$ and $j$, the threshold function $\mathrm{Th}^k_{\ge j}$ has a fan-in-two De Morgan circuit of size $O(k\log(k+2))$ and depth $O(\log(k+2))$. Consequently every family of threshold functions, in particular majority, belongs to (nonuniform) $\mathsf{NC}^1$, and $\mathsf{TC}^0\subseteq\mathsf{NC}^1$.

## Proof sketch

Compute the Hamming weight in logarithmic depth with carry-save trees and compare it with the constant $j$ by a logarithmic-depth comparator. Replacing every majority gate of a constant-depth threshold circuit by such a subcircuit multiplies the depth by $O(\log n)$.

## Depends on

- [The AC, TC and AC[q] hierarchies](ac-tc-and-acq-hierarchies.md)

## Proof depends on

- [Carry-save addition and logarithmic-depth bit counting](carry-save-addition-and-bit-counting.md)

## Sources

- Ashok K. Chandra, Larry Stockmeyer, Uzi Vishkin, "Constant Depth Reducibility", SIAM Journal on Computing, 1984.
- Heribert Vollmer, "Introduction to Circuit Complexity: A Uniform Approach", Springer, 1999.
