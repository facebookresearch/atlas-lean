# The bi-infinite Post correspondence problem is in Σ⁰₂ but not in Π⁰₁

Deciding whether two morphisms agree, up to a shift, on some bi-infinite word is undecidable and lies at the second level of the arithmetical hierarchy: the problem is in $\Sigma^0_2$ and is $\Sigma^0_1$-hard, hence not in $\Pi^0_1$.

A *bi-infinite word* over $A$ is a sequence $w=(w(i))_{i\in\mathbb Z}$ of letters of $A$, and a morphism $h:A^*\to B^*$ extends to bi-infinite words by concatenating the images $h(w(i))$ in order. Two bi-infinite words $x$ and $y$ are *equal* if they agree up to a shift: there is $s\in\mathbb Z$ with $x(i)=y(i+s)$ for all $i\in\mathbb Z$.

**Theorem.** The *bi-infinite Post correspondence problem* ($\mathbb Z\mathrm{PCP}$) asks, given morphisms $h,g:A^*\to B^*$, whether some bi-infinite word $w$ over $A$ satisfies $h(w)=g(w)$. The set of instances with a solution, coded as a set of natural numbers, lies in $\Sigma^0_2\setminus\Pi^0_1$ (Theorem 2 of the source).

An instance is given by the finite lists of images $h(a), g(a) \in B^*$, $a \in A$, coded by a natural number. The source places no nonerasing condition on $h$ and $g$ and does not discuss the case where $h(w)$ or $g(w)$ fails to be a bi-infinite word.

In particular $\mathbb Z\mathrm{PCP}$ is not co-recursively enumerable, unlike the [infinite Post correspondence problem](infinite-pcp-is-pi01-complete.md), which is $\Pi^0_1$-complete. Whether it is $\Sigma^0_2$-complete is left open by the source.

## Depends on

- [The arithmetical class $\Sigma_n$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [The arithmetical class $\Pi_n$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Co-recognizability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Not in $\Pi^0_1$: the known proof of undecidability of $\mathbb Z\mathrm{PCP}$ by Halava, Harju and Sahla (V. Halava, T. Harju and E. Sahla, "A new proof for undecidability of the bi-infinite Post correspondence problem", *Fundamenta Informaticae* 154(1–4):167–176, 2017, as cited in the source) reduces the halting problem, which is $\Sigma^0_1$-complete, to it, so $\mathbb Z\mathrm{PCP}$ is $\Sigma^0_1$-hard. In $\Sigma^0_2$: a candidate solution $\cdots i_{-1}i_0i_1\cdots$ is folded into the infinite word $(i_0,i_0)(i_1,i_{-1})(i_2,i_{-2})\cdots$ over pairs of letters, and a deterministic Turing machine with co-Büchi acceptance checks it against shifts $s=0,1,-1,2,-2,\dots$ in turn, entering a rejecting state each time it finds a mismatch and moving to the next shift. It visits rejecting states only finitely often iff some shift works, so the solutions form an effective $\Sigma^0_2$ set of infinite words, and by a theorem of Cenzer and Remmel nonemptiness of such sets is a $\Sigma^0_2$ property.

## Sources

- Olivier Finkel, Vesa Halava, Tero Harju and Esa Sahla, "On bi-infinite and conjugate post correspondence problems", *RAIRO - Theoretical Informatics and Applications* 57 (2023), article 7, doi:[10.1051/ita/2023008](https://doi.org/10.1051/ita/2023008); read in arXiv:2111.04484v3 ([arXiv](https://arxiv.org/abs/2111.04484v3)), whose numbering is used: the definition of $\mathbb Z\mathrm{PCP}$ and of equality up to a shift (Problem 2 and the remark after it, introduction), Theorem 2 (final section) and its proof, and the concluding open question.
