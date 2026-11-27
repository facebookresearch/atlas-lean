# Threshold functions by quadratic-size De Morgan circuits

Let $f_0,\dots,f_{n-1}$ be Boolean functions already available as wires, and let $\mathrm{Th}_{\ge j}(i)$ denote the function "at least $j$ of $f_0,\dots,f_{i-1}$ are true". The recursion $\mathrm{Th}_{\ge j+1}(i+1)=\mathrm{Th}_{\ge j+1}(i)\vee\bigl(f_i\wedge \mathrm{Th}_{\ge j}(i)\bigr)$ computes all functions $\mathrm{Th}_{\ge j}(n)$, $1\le j\le k$, with at most $2nk$ additional AND and OR gates. In particular every symmetric Boolean function of $n$ variables has a De Morgan circuit of size $O(n^2)$.

## Proof sketch

Dynamic programming over $(i,j)$ with one AND and one OR per table entry; a symmetric function is a disjunction of differences of consecutive thresholds.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)
- [Linear threshold function](../../../../../Combinatorics/boolean-functions/majority-is-least-stable-conjecture/is-linear-threshold-function.md)
- [Threshold gates and the basis of threshold circuits](../../../parallel-circuit-hierarchies/threshold-gates-and-threshold-circuits.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987.
