# Antimorphic permutations, input-preserving transducers and the θ-Post correspondence problem

An antimorphic permutation maps a word to the reversed word of permuted letters, as Watson–Crick complementation does on DNA; a
transducer is θ-input-preserving if it can always output θ of its input and θ-input-altering if it never can, and the θ-Post correspondence
problem matches one concatenation against θ of another.

**Antimorphic permutations.** Let $\Sigma_k = \{0, \dots, k-1\}$. A permutation $\theta$ of $\Sigma_k$ extends to words either as a *morphic permutation*,
$\theta(uv) = \theta(u)\theta(v)$, or as an *antimorphic permutation*, $\theta(uv) = \theta(v)\theta(u)$, for all $u, v \in \Sigma_k^*$. The antimorphic extension of the
identity is the mirror image; on the DNA alphabet $\{A, C, G, T\}$ the involution exchanging $A \leftrightarrow T$ and $C \leftrightarrow G$, extended antimorphically, is
Watson–Crick complementation.

**Transducers.** Here a *transducer* is a tuple $t = (Q, \Sigma, E, I, F)$ with input and output alphabet $\Sigma$, a finite set $Q$ of states, initial and final
states $I, F \subseteq Q$, and finitely many edges between states labeled by pairs $(u, v) \in \Sigma^* \times \Sigma^*$; it realizes the pairs $(x, y)$ obtained by
concatenating the inputs and the outputs along a path from an initial to a final state, and $t(w)$ is the set of outputs on input $w$. For an antimorphic
permutation $\theta$, the transducer is *$\theta$-input-preserving* if $\theta(w) \in t(w)$ for every nonempty word $w$, and *$\theta$-input-altering* if $\theta(w) \notin t(w)$ for
every nonempty word $w$. Such transducers describe code properties: an input-altering transducer describes the property of languages $L$ in which no
word is mapped to a different word of $L$, as for DNA codes avoiding unwanted hybridization.

**The θ-Post correspondence problem.** For a fixed antimorphic permutation $\theta$ of $\Sigma_k$, the *$\theta$-PCP* asks, given nonempty words
$\alpha_0, \dots, \alpha_{\ell-1}$ and $\beta_0, \dots, \beta_{\ell-1}$ over $\Sigma_k$, whether some nonempty sequence $i_1, \dots, i_n$ of indices satisfies

$$
\alpha_{i_1} \alpha_{i_2} \cdots \alpha_{i_n} = \theta(\beta_{i_1} \beta_{i_2} \cdots \beta_{i_n}).
$$

## Depends on

- [The Post correspondence problem](../../../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)
- [Rational relations and transducers](../rational-relations-and-transducers.md)

## Proof depends on

None.

## Sources

- L. Kari, S. Konstantinidis and S. Kopecki, "Transducer descriptions of DNA code properties and undecidability of antimorphic problems", *Information and Computation* 259:237–258, 2018, doi:10.1016/j.ic.2017.09.004; conference version in *Descriptional Complexity of Formal Systems (DCFS 2015)*, Lecture Notes in Computer Science 9118, pp. 141–152, 2015, doi:10.1007/978-3-319-19225-3_12. Read in arXiv:1503.00035v1: Section 2.1 (morphic and antimorphic permutations), Section 2.2 (transducers, input-preserving and input-altering transducers and the properties they describe) and the definition of the $\theta$-PCP in Section 6.
