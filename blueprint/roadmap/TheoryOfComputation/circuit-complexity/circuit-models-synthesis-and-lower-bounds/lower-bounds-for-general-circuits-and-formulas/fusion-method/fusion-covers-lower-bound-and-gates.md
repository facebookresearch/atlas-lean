# Semifilter covers lower-bound the AND count of monotone circuits

Let $f$ be a nonconstant Boolean function on $n$ variables and let $C$ be a monotone circuit computing $f$ from the supplied functions (input literals, both polarities allowed, supplied for free), with $t$ fan-in-two AND gates. Then the pairs $(A\setminus T,B\setminus T)$, where $A,B$ are the true sets of the arguments of an AND gate and $T=f^{-1}(1)$, form a pair cover of length $t$ for the instance with target $T$ and the literal sets as supplied sets. Hence the cover complexity of $f$ lower-bounds the number of AND gates, and De Morgan circuit size, since the dual-rail translation of a De Morgan circuit has one AND gate for each AND or OR gate.

## Proof sketch

Fix a semifilter $F$ above $u\in T$, and call a wire with true set $S$ *good* if $u\in S$ implies $S\setminus T\in F$. Inputs are good because $F$ is above $u$, OR gates preserve goodness by upward closure, and the output (true set $T\ni u$, with $T\setminus T=\emptyset\notin F$) is bad; so some AND gate has good arguments $A,B$ with $u\in A\cap B$ and a bad output, that is, $F$ contains $A\setminus T$ and $B\setminus T$ but not their intersection.

## Depends on

- [Semifilters and semifilter (fusion) covers](semifilters-and-fusion-covers.md)

## Proof depends on

- [Dual-rail translation of De Morgan circuits into monotone circuits](../../../monotone-circuit-complexity/dual-rail-translation-to-monotone-circuits.md)

## Sources

- Alexander A. Razborov, "On the Method of Approximations", Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing, 167–176, 1989.
- Mauricio Karchmer, "On Proving Lower Bounds for Circuit Size", Proceedings of the 8th Annual Structure in Complexity Theory Conference, 112–118, 1993.
- Bruno P. Cavalar, Igor C. Oliveira, "Boolean Circuit Complexity and Two-Dimensional Cover Problems", ACM Transactions on Computation Theory, 2025 (Theorem 22).
