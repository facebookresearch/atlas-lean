# Whether a transducer is θ-input-preserving or θ-input-altering is undecidable

For every fixed antimorphic permutation $\theta$ of an alphabet with at least two letters, no algorithm decides whether a given transducer can
output $\theta(w)$ on every input $w$, nor whether it never can.

**Theorem (Kari, Konstantinidis and Kopecki).** Let $\theta$ be a fixed antimorphic permutation of $\Sigma_k$ with $k \ge 2$, and consider transducers over $\Sigma_k$ in the sense of
[antimorphic permutations, input-preserving transducers and the θ-Post correspondence problem](antimorphic-permutations-input-preserving-transd.md).

1. It is undecidable whether a given transducer is $\theta$-input-preserving.
2. It is undecidable whether a given transducer is $\theta$-input-altering, already for one-state transducers.

As a consequence, for every such $\theta$ it is undecidable, given a transducer describing a property, whether the empty language is maximal for that
property, since $\emptyset$ is maximal exactly when the transducer is $\theta$-input-preserving. By contrast, satisfaction is decidable: given a regular language $L$, a transducer $t$ and an antimorphic involution $\theta$, it can be decided whether $L$ satisfies the property described by $t$ with respect to $\theta$.

## Depends on

- [Antimorphic permutations, input-preserving transducers and the θ-Post correspondence problem](antimorphic-permutations-input-preserving-transd.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)
- [The θ-Post correspondence problem is undecidable for every antimorphic permutation](the-post-correspondence-problem-is-undecidable-f.md)

## Expansion

For input-preserving transducers, the proof reduces the Post correspondence problem: from an instance it builds, as the union of three components,
a transducer that accepts every pair $(w, \theta(w))$ unless $w$ is the binary encoding of a solution word followed by its index sequence, so the
transducer is $\theta$-input-preserving exactly when the instance has no solution. For input-altering transducers, a $\theta$-PCP instance
$\alpha_0, \dots, \alpha_{\ell-1}$, $\beta_0, \dots, \beta_{\ell-1}$ has a solution if and only if the one-state transducer with loops labeled
$(\alpha_i, \theta^2(\beta_i))$ is not $\theta$-input-altering.

## Sources

- L. Kari, S. Konstantinidis and S. Kopecki, "Transducer descriptions of DNA code properties and undecidability of antimorphic problems", *Information and Computation* 259:237–258, 2018, doi:10.1016/j.ic.2017.09.004; read in arXiv:1503.00035v1: the theorem on $\theta$-input-preserving transducers in Section 5 with its proof and the corollary on maximality after it, and the corollary on $\theta$-input-altering transducers in Section 6.
