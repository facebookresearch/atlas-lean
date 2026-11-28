# Post embedding with combined directness constraints is Σ⁰₁-complete

The regular Post embedding problem, which asks for a word of a regular language whose first image is a subword of its second, is decidable even
with partial directness; combining directness with codirectness, or requiring codirectness on the suffixes in a deterministic context-free or Presburger-definable set, makes it $\Sigma^0_1$-complete.

For a word $x$, write $x \sqsubseteq y$ if $x$ is a *subword* (scattered subword) of $y$, that is, $x$ is obtained from $y$ by erasing letters. Given morphisms $u, v : \Sigma^* \to \Gamma^*$ and a regular language $R \subseteq \Sigma^*$, the *regular
Post embedding problem* (PEP) asks whether some $\sigma \in R$ satisfies $u(\sigma) \sqsubseteq v(\sigma)$, by analogy with the [Post correspondence problem](exists-not-tm2-decidable-pcp.md), which asks for equality. Variants constrain prefixes and suffixes of a
solution $\sigma \in R$ with $u(\sigma) \sqsubseteq v(\sigma)$:

- $\mathrm{PEP}^{\mathrm{dir\text{-}codir}}$: $u(\tau) \sqsubseteq v(\tau)$ and $u(\tau') \sqsubseteq v(\tau')$ for every decomposition $\sigma = \tau\tau'$ (the solution is both direct and codirect);
- $\mathrm{PEP}^{\mathrm{partial\text{-}codir}}$ with an extra language $R'$: $u(\tau) \sqsubseteq v(\tau)$ for every suffix $\tau$ of $\sigma$ that belongs to $R'$; with $R'$ regular this problem, like its prefix version, is decidable.

An instance gives the alphabets $\Sigma, \Gamma$, the morphisms $u, v$ by the images of the letters, $R$ by a finite automaton and, where present, $R'$ by a deterministic pushdown automaton or by a Presburger formula (equivalently a semilinear set given by base and period vectors) for its Parikh images.

**Theorem (Karandikar and Schnoebelen).**

1. $\mathrm{PEP}^{\mathrm{dir\text{-}codir}}$ is $\Sigma^0_1$-complete (Theorem 20 of the source).
2. $\mathrm{PEP}^{\mathrm{partial\text{-}codir}}$ is $\Sigma^0_1$-complete when $R'$ may be any deterministic context-free language, and when $R'$ may be any Presburger-definable language (all words whose Parikh image lies in a given semilinear set), $R$ still being
   regular (Theorem 18).

Both problems are clearly in $\Sigma^0_1$, so the content is hardness. In contrast, PEP itself is decidable but not primitive recursive, and the same holds for PEP with partial directness or partial codirectness given by regular languages, which the
source proves decidable through Higman's lemma and a length function theorem.

## Depends on

- [Deterministic pushdown automaton](../../context-free-languages/grammars-and-pushdown-automata/deterministic-context-free-languages/is-deterministic.md)
- [Deterministic context-free language](../../context-free-languages/grammars-and-pushdown-automata/deterministic-context-free-languages/is-deterministic-context-free.md)
- [Parikh image of a language](../../context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/parikh-image.md)
- [Semilinear set of vectors](../../context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/is-semilinear.md)
- [The arithmetical class $\Sigma_n$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Every recognizable predicate many-one reduces to the halting set](../../degrees-and-hierarchies/completeness-of-the-halting-set/many-one-reducible-halting-set.md)
- [The Post correspondence problem is undecidable](exists-not-tm2-decidable-pcp.md)

## Expansion

Item 2 reduces the Post correspondence problem: from an instance $(u, v)$ one builds an instance with two marker letters and a set $R'$ of suffixes whose images have different lengths, which is deterministic context-free and Presburger-definable, so that
codirectness on $R'$ forces equal lengths and hence equality $u(\sigma) = v(\sigma)$. Item 1 reduces the reachability problem for length-preserving semi-Thue systems. A good expansion links pages for the $\Sigma^0_1$-completeness of that reachability problem and of the Post correspondence problem, which the hardness parts use (Theorems 18 and 20 of the source).

## Sources

- P. Karandikar and P. Schnoebelen, "Generalized Post embedding problems", *Theory of Computing Systems* 56(4):697–716, 2015, doi:10.1007/s00224-014-9561-9; read in arXiv:1109.1691v4: the two undecidability theorems of the section on undecidability for PEP with directness and codirectness and other extensions with their proofs, the definitions of PEP with partial directness and codirectness, and the decidability results of the preceding sections.
