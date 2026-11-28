# θ-Post correspondence problem

For a fixed antimorphic permutation θ, the θ-Post correspondence problem asks whether some nonempty index sequence makes a concatenation of the first list of words equal to θ of the corresponding concatenation of the second list.

**The θ-Post correspondence problem.** For a fixed antimorphic permutation $\theta$ of $\Sigma_k$, the *$\theta$-PCP* asks, given nonempty words
$\alpha_0, \dots, \alpha_{\ell-1}$ and $\beta_0, \dots, \beta_{\ell-1}$ over $\Sigma_k$, whether some nonempty sequence $i_1, \dots, i_n$ of indices satisfies

$$
\alpha_{i_1} \alpha_{i_2} \cdots \alpha_{i_n} = \theta(\beta_{i_1} \beta_{i_2} \cdots \beta_{i_n}).
$$

The ordinary Post correspondence problem compares the two concatenations directly; here the second one is read through θ, which for an antimorphic permutation also reverses it.

## Depends on

- [Antimorphic permutations and input-preserving transducers](antimorphic-permutations-input-preserving-transd.md)
- [The Post correspondence problem](../../../../undecidable-problems/post-correspondence-problem/pcp.md)

## Proof depends on

None.

## Sources

- L. Kari, S. Konstantinidis and S. Kopecki, "Transducer descriptions of DNA code properties and undecidability of antimorphic problems", *Information and Computation* 259:237–258, 2018, doi:10.1016/j.ic.2017.09.004; read in arXiv:1503.00035v1: Definition 27 in Section 6, with the numbering of that version.
