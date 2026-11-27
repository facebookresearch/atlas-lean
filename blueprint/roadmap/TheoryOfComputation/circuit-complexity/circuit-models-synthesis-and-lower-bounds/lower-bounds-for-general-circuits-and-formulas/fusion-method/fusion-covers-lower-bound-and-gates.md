# Semifilter covers lower-bound the AND count of monotone circuits

Let $f$ be a Boolean function on $n$ variables and let $C$ be a monotone circuit computing $f$ from the supplied functions (input literals, both polarities allowed, supplied for free), with $t$ AND gates. Then the pairs (argument sets of the AND gates, read as sets of inputs) form a semifilter cover of length $t$ for the problem with target $f^{-1}(1)$ and supplied sets the true sets of the literals. Hence the cover complexity of $f$ lower-bounds the number of AND gates, and De Morgan circuit size, since the dual-rail translation of a De Morgan circuit has one AND gate for each AND or OR gate.

## Proof sketch

Given a witness $(u,F)$, call a wire with true set $S$ *good* if $u\in S$ implies that $F$ accepts $S\setminus T$. Inputs are good by the witness condition, OR gates preserve goodness by monotonicity of $F$, and the output (true set $T\ni u$, with $T\setminus T=\emptyset$ rejected) is bad; so some AND gate has good arguments and a bad output, i.e. its argument pair defeats the witness.

## Depends on

- [Semifilters and semifilter (fusion) covers](semifilters-and-fusion-covers.md)

## Proof depends on

- [Dual-rail translation of De Morgan circuits into monotone circuits](../../../monotone-circuit-complexity/dual-rail-translation-to-monotone-circuits.md)

## Sources

- Alexander A. Razborov, "On the Method of Approximations", Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing, 1989.
- Igor Carboni Oliveira, "Notes on the Method of Approximations and the Emergence of the Fusion Method", 2018.
