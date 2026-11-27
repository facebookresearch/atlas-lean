# Intractability transfers between the GAC decision problems

On any one constraint type, the problems of deciding whether a value has a support, deciding whether a nonempty GAC subdomain exists, and computing the GAC closure are polynomial-time reducible to each other with polynomially many oracle calls; NP-hardness of recognising GAC domains or the largest GAC subdomain passes down to support checking in the same sense.

Let $\mathcal C$ be a constraint type with encoded instances and a uniform polynomial-time evaluator, and consider the five [decision problems of generalized arc consistency](gac-reasoning-problems.md) on $\mathcal C$. A **polynomial-time Turing reduction** from $Q_1$ to $Q_2$ is a polynomial-time algorithm that solves $Q_1$ using an oracle for $Q_2$ (for the function problem GACDomain, an oracle returning its output); all oracle calls below are on the same constraint $C$ with modified domains, and for an instance with domain $D$ they number at most $1+\sum_{X}|D(X)|$. Call $Q$ **Turing-NP-hard** if every problem in NP has a polynomial-time Turing reduction to it.

1. GACSupport($\mathcal C$), NoGACWipeOut($\mathcal C$) and GACDomain($\mathcal C$) are pairwise polynomial-time Turing reducible to each other. Hence one of them is Turing-NP-hard iff all are, and one of them is solvable in polynomial time iff all are.
2. MaxGAC($\mathcal C$) is polynomial-time Turing reducible to GACSupport($\mathcal C$).
3. IsItGAC($\mathcal C$) has a polynomial-time many-one reduction to MaxGAC($\mathcal C$), and GACSupport($\mathcal C$) has one to NoGACWipeOut($\mathcal C$).

Consequently, Turing-NP-hardness of MaxGAC or of IsItGAC implies Turing-NP-hardness of GACSupport, NoGACWipeOut and GACDomain, and polynomial-time solvability transfers along the same reductions in the opposite direction. In particular, if NoGACWipeOut is NP-hard under many-one reductions (the usual way hardness of propagating a constraint type is shown), no polynomial-time algorithm enforces GAC on the type unless P $=$ NP. These implications do not reverse: hardness of the exact problems IsItGAC and MaxGAC is not obtained from hardness of NoGACWipeOut by these arguments.

## Depends on

- [Decision problems of generalized arc consistency](gac-reasoning-problems.md): the five problems and the encoding model.
- [Polynomial-time many-one reduction](../../np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md): the many-one reductions in item 3.

## Proof depends on

- [Generalized arc consistency](generalized-arc-consistency.md): uniqueness of the GAC closure and its description as the set of supported values.

## Expansion

Write $D|_{X=v}$ for $D$ with $D(X)$ replaced by $\{v\}$.

- GACSupport$[C,D,X,v]$ is NoGACWipeOut$[C,D|_{X=v}]$ (many-one), and it is "GACDomain$[C,D|_{X=v}]$ is not empty" (one function-oracle call).
- NoGACWipeOut$[C,D]$: fix one $X\in\mathrm{var}(C)$ and ask GACSupport$[C,D,X,v]$ for every $v\in D(X)$; some answer is yes iff $C$ has an allowed tuple in $D$ (no call is needed when $D(X)=\emptyset$).
- GACDomain$[C,D_0]$: ask GACSupport$[C,D_0,X,v]$ for every variable $X$ and value $v\in D_0(X)$ and keep the values answered yes.
- MaxGAC$[C,D_0,D]$: compute the set $D'$ of values of $D_0$ supported in $D_0$ by GACSupport calls and answer yes iff $D'=D$.
- IsItGAC$[C,D]$ is MaxGAC$[C,D,D]$ (many-one).

Item 1 combines the first three bullets, item 2 is the fourth and item 3 the first and fifth. If a problem $Q_1$ Turing-reduces to $Q_2$ and every NP problem Turing-reduces to $Q_1$, composing gives Turing reductions to $Q_2$.

Bessiere, Hebrard, Hnich and Walsh define a reduction in §2 as a program making "at most a constant number" of oracle calls, but the proofs of their Lemmas 2–4 make one call per value, and the text after their dependency figure says that each arrow "means that A can be rewritten as a polynomial number of calls to B". Bessiere's handbook chapter states the same dependencies (its Theorem 26) with the same polynomial-number-of-calls reading. The statement above therefore uses polynomial-time Turing reductions, not constant-query or many-one reductions, except for the two one-shot transformations.

## Sources

- C. Bessiere, E. Hebrard, B. Hnich and T. Walsh, "The complexity of reasoning with global constraints", *Constraints* 12(2) (2007), 239–259, doi:10.1007/s10601-006-9007-3. Reductions and transformations defined in §2; Lemmas 1–4 and Corollaries 1–2 with proofs, the dependency summary of Fig. 1 and the paragraph following it, in §3.3; §4 remark on exact problems; arXiv:0903.1139v1, [https://arxiv.org/abs/0903.1139v1](https://arxiv.org/abs/0903.1139v1).
- C. Bessiere, "Constraint propagation", in F. Rossi, P. van Beek and T. Walsh (eds.), *Handbook of Constraint Programming*, Elsevier (2006), chapter 3, doi:10.1016/S1574-6526(06)80007-6; numbering from the author's version, Technical Report LIRMM 06020 (March 2006), [https://www.lirmm.fr/~bessiere/Site/stock/TR06020.pdf](https://www.lirmm.fr/~bessiere/Site/stock/TR06020.pdf), §4.1, Theorem 26 (dependencies in the NP-hardness of GAC questions), Fig. 2 and the following paragraph.
