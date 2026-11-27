# Semi-ultrafilter covers characterize conondeterministic AND complexity

Call a semifilter a *semi-ultrafilter* if for every set $A$ it accepts exactly one of $A$ and its complement. For a Boolean function $f$, let $\mathrm{coAND}(f)$ be the least number of AND gates of a monotone verifier circuit $V(x,r)$ (literals free) with $f(x)=\forall r\,V(x,r)$. Then semi-ultrafilter covers of $f$ of length $t$ give such verifiers with $2t$ auxiliary bits and exactly $3t$ AND gates, and conversely every verifier with $t$ AND gates yields a semi-ultrafilter cover of length $t$. Thus semi-ultrafilter cover complexity equals conondeterministic AND complexity up to a factor $3$.

## Proof sketch

From a verifier: for each false input choose a rejecting auxiliary assignment; a semi-ultrafilter above a true input selects a fused auxiliary reference that the verifier accepts, and pulling back its AND pairs gives a cover. From a cover: two auxiliary bits per pair label its components, and three AND gates per pair check consistency of the guessed labels.

## Depends on

- [Semifilters and semifilter (fusion) covers](semifilters-and-fusion-covers.md)
- [Nondeterministic and conondeterministic circuits](../../circuit-models-and-classes/simulations-between-circuit-bases/nondeterministic-and-conondeterministic-circuits.md)

## Proof depends on

- [Semifilter covers lower-bound the AND count of monotone circuits](fusion-covers-lower-bound-and-gates.md)

## Sources

- Alexander A. Razborov, "On the Method of Approximations", Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing, 1989.
- Igor Carboni Oliveira, "Notes on the Method of Approximations and the Emergence of the Fusion Method", 2018.
