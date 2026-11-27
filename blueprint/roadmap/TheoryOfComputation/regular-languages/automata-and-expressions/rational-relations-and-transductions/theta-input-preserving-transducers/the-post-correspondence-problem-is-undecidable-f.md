# The θ-Post correspondence problem is undecidable for every antimorphic permutation

For every fixed antimorphic permutation $\theta$ of an alphabet with at least two letters, no algorithm decides whether a list of pairs of
words has a sequence whose first concatenation equals $\theta$ of the second.

**Theorem (Kari, Konstantinidis and Kopecki).** For every fixed antimorphic permutation $\theta$ of $\Sigma_k$ with $k \ge 2$, the
[$\theta$-Post correspondence problem](antimorphic-permutations-input-preserving-transd.md) is undecidable.

This includes the mirror image (the antimorphic extension of the identity) and Watson–Crick complementation on the DNA alphabet. The
alphabet size $k$ and the permutation are fixed; the word pairs are the input.

## Depends on

- [Antimorphic permutations, input-preserving transducers and the θ-Post correspondence problem](antimorphic-permutations-input-preserving-transd.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof gives an effective reduction from the Post correspondence problem over the binary alphabet: each instance over $\{0, 1\}$ is turned into
a $\theta$-PCP instance over $\Sigma_k$, encoding letters so that a word equals $\theta$ of another word exactly when the underlying binary words agree, and
the original instance has a solution if and only if the new one has.

## Sources

- L. Kari, S. Konstantinidis and S. Kopecki, "Transducer descriptions of DNA code properties and undecidability of antimorphic problems", *Information and Computation* 259:237–258, 2018, doi:10.1016/j.ic.2017.09.004; read in arXiv:1503.00035v1: the theorem on the $\theta$-PCP in Section 6 with its proof.
