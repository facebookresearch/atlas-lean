# Decipherability of two-sided directed figure codes is undecidable

No algorithm decides whether a given two-sided set of directed figures is a uniquely, multiset, set or numerically decipherable
code.

**Theorem.** Let $X$ be a two-sided code of [directed figures](directed-figures-and-decipherable-directed-figur.md) over $\Sigma$,
with catenation without merging. It is undecidable whether $X$ is a UD code; likewise it is undecidable whether $X$ is an MSD code,
whether it is an SD code, and whether it is an ND code.

For one-sided codes all four kinds of decipherability are decidable, as they are for two-sided codes whose translation vectors are
parallel; so the undecidability needs translation vectors that do not all lie in one open half-plane bounded by a line through the origin (the source's constructions for uniquely, multiset and set decipherability use vectors from a closed half-plane) and are not all parallel. With
$m$-catenation, two-sided codes are never ND, MSD or UD $m$-codes, so those cases are decidable trivially; whether a two-sided code is an SD $m$-code is left open by the source. Being two-sided is itself decidable, as it asks for a nonnegative integer solution of a homogeneous linear system.

## Depends on

- [Directed figures and decipherable directed figure codes](directed-figures-and-decipherable-directed-figur.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof reduces the Post correspondence problem. Over the one-letter alphabet $\{a\}$, it builds *directed hooked squares*, large
squares whose sides carry hooks and dents of prescribed heights, so that two figures fit side by side only when their hooks match.
From a PCP instance it builds a two-sided code whose figures encode the letters of the words $u_i$ and $v_i$; a figure equal to two
different catenations of codewords exists exactly when the instance has a solution. The argument for UD codes carries over to MSD and
SD codes, and since the two factorizations built there have the same number of figures, an additional technique is needed for ND codes: each square is replaced by 25 squares with new labels, connected into one figure on one side and left separate on the other. The
undecidability of unique decipherability for two-sided codes was known from earlier work, which the source cites. A good expansion links a page for the encoding of Post correspondence instances by directed hooked squares and its correctness.

## Sources

- W. Moczurad, "Decidability of multiset, set and numerically decipherable directed figure codes", *Discrete Mathematics and Theoretical Computer Science* 19(1), paper 11, 2017, doi:10.23638/DMTCS-19-1-11; read in arXiv:1604.02167v3: Theorem 4 with its proof in Section 4, Theorems 2 and 3 (the decidable cases), Theorem 1 (a necessary condition for two-sided codes) and the summary table in Section 4.
