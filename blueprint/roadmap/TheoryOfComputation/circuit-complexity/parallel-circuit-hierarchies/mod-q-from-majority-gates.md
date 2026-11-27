# MOD_q gates from majority gates: AC^i[q] is contained in TC^i

Over a basis containing the unbounded fan-in basis, $\mathrm{MOD}_q$ on $n$ bits is computed by a circuit with one majority gate per threshold, of size $O(n)$ per term and constant depth: $\mathrm{MOD}_q(x)=\bigvee_{k\le n,\,q\nmid k}[\,|x|=k\,]$ and $[\,|x|=k\,]=\mathrm{Th}_{\ge k}(x)\wedge\neg\mathrm{Th}_{\ge k+1}(x)$, where each threshold is a majority of the input padded with constants. A single $\mathrm{MOD}_q$ gate becomes a circuit of $O(n)$ gates and $O(n^2)$ wires, of depth at most five. Consequently $\mathsf{AC}^i[q]\subseteq\mathsf{TC}^i$ for every $i$ and every $q\ge2$.

## Proof sketch

Padding with $n+2$ constants turns majority on $2n+2$ bits into any threshold on $n$ bits; symmetric gates depend only on the count of true arguments (modulo $q$ for $\mathrm{MOD}_q$), so repeated wires are handled by multiplicity bookkeeping.

## Depends on

- [The AC, TC and AC[q] hierarchies](ac-tc-and-acq-hierarchies.md)

## Sources

- Ashok K. Chandra, Larry Stockmeyer, Uzi Vishkin, "Constant Depth Reducibility", SIAM Journal on Computing, 1984.
- Heribert Vollmer, "Introduction to Circuit Complexity: A Uniform Approach", Springer, 1999.
