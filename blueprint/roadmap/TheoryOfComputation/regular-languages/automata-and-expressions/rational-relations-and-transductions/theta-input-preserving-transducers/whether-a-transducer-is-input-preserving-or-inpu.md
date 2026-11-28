# Whether a transducer is θ-input-preserving or θ-input-altering is undecidable

For every fixed antimorphic permutation $\theta$ of an alphabet with at least two letters, no algorithm decides whether a given transducer can
output $\theta(w)$ on every input $w$, nor whether it never can.

**Theorem (Kari, Konstantinidis and Kopecki).** Let $\theta$ be a fixed antimorphic permutation of $\Sigma_k$ with $k \ge 2$, and consider transducers over $\Sigma_k$ in the sense of
[antimorphic permutations and input-preserving transducers](antimorphic-permutations-input-preserving-transd.md).

1. It is undecidable whether a given transducer is $\theta$-input-preserving.
2. It is undecidable whether a given transducer is $\theta$-input-altering, already for one-state transducers.

As a consequence, for every such $\theta$ it is undecidable, given a transducer $t$, whether the empty language is maximal for the strict property $S_{\theta,t}$ of the languages $L$ with $\theta(L) \cap t(L) = \varnothing$, since $\emptyset$ is maximal for it exactly when $t$ is $\theta$-input-preserving. By contrast, for the weak property $W_{\theta,t}$ of the source, satisfaction is decidable: given a regular language $L$, a transducer $t$ and an antimorphic involution $\theta$, it can be decided whether $L$ satisfies $W_{\theta,t}$.

## Depends on

- [Antimorphic permutations and input-preserving transducers](antimorphic-permutations-input-preserving-transd.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

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

- L. Kari, S. Konstantinidis and S. Kopecki, "Transducer descriptions of DNA code properties and undecidability of antimorphic problems", *Information and Computation* 259:237–258, 2018, doi:10.1016/j.ic.2017.09.004; read in arXiv:1503.00035v1: Theorem 25 in Section 5.2 with its proof and Corollary 26 (maximality) after it, Corollary 29 ($\theta$-input-altering transducers) in Section 6, Definition 5 (the properties $S_{\theta,t}$ and $W_{\theta,t}$) in Section 3, and Theorem 21 (satisfaction) in Section 5.1, with the numbering of that version.
