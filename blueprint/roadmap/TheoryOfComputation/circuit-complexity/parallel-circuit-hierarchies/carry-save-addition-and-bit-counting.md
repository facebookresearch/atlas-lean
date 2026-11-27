# Carry-save addition and logarithmic-depth bit counting

A $3$-to-$2$ carry-save adder maps three $w$-bit words $x,y,z$ to the bitwise sum $x\oplus y\oplus z$ and the shifted majority word $2\cdot\mathrm{MAJ}(x,y,z)$, preserving $x+y+z$ modulo $2^w$, with $O(w)$ gates and constant depth (at most $6$). Combining $k$ one-bit inputs along a balanced tree of carry-save reducers and finishing with one carry-lookahead addition yields a fan-in-two De Morgan circuit computing the Hamming weight of $k$ bits with $O(k\log(k+2))$ gates and depth $O(\log(k+2))$ (the shift by $2$ keeps both bounds meaningful for $k\le1$, where the weight is a constant or the input bit itself).

## Proof sketch

Bitwise, $x_i+y_i+z_i=(x_i\oplus y_i\oplus z_i)+2\,\mathrm{MAJ}(x_i,y_i,z_i)$, so carries never propagate inside a reducer; a balanced tree has logarithmic depth and the final carry-lookahead addition has logarithmic depth.

## Depends on

- [The AC, TC and AC[q] hierarchies](ac-tc-and-acq-hierarchies.md)
- [Kogge–Stone carry-lookahead adder](../kogge-stone-adder/carry-lookahead-adder.md)

## Sources

- Ashok K. Chandra, Larry Stockmeyer, Uzi Vishkin, "Constant Depth Reducibility", SIAM Journal on Computing, 1984.
- Heribert Vollmer, "Introduction to Circuit Complexity: A Uniform Approach", Springer, 1999.
- Richard E. Ladner, Michael J. Fischer, "Parallel Prefix Computation", Journal of the ACM, 1980.
