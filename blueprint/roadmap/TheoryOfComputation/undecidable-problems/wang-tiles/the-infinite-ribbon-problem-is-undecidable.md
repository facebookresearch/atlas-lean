# The infinite ribbon problem is undecidable

No algorithm decides whether a finite set of Wang tiles admits an infinite ribbon, a non-self-crossing path of tiles in the plane, indexed by all integers, whose consecutive tiles match along their common edges; consequently it is undecidable whether a tile set self-assembles an infinite supertile.

**Ribbons.** A *tile* is a quadruple $t=(t_N,t_E,t_S,t_W)$ of glues from a finite set, and a *tile system* $T$ is a finite set of tiles, which cannot be rotated (see [Wang tiles and valid tilings](wang-tiles-and-valid-tilings.md)); $t$ *sticks* on the north to $t'$ if $t_N=t'_S$, and similarly for the other sides. A *path* is a map $P:I\to\mathbb Z^2$ on a set $I$ of consecutive integers such that $P(i)$ and $P(i+1)$ are adjacent for all $i,i+1\in I$. A *$T$-ribbon* is a pair $(P,r)$ of a one-to-one path $P$ and a map $r:\mathrm{range}(P)\to T$ such that consecutive tiles match on their shared edge: if $P(i+1) = P(i) + (0, 1)$ then $r(P(i))_N = r(P(i+1))_S$, if $P(i+1) = P(i) + (1, 0)$ then $r(P(i))_E = r(P(i+1))_W$, and similarly for the other two directions (the source states this with its relation "abuts", §2); it is *infinite* if $I=\mathbb Z$, and *semi-infinite* if $I$ is infinite with a least or a greatest element (§2 of the source). Only consecutive tiles of the path have to match, not all adjacent ones.

**Theorem (Adleman, Kari, Kari, Reishus and Sosík).** The set of tile systems $T$ for which there exists an infinite $T$-ribbon is undecidable (Theorem 4.2).

As a consequence, the same paper shows that the sets of tile systems that admit an infinite supertile, and of tile systems that admit infinitely many pairwise non-equivalent finite supertiles, are undecidable (Theorem 5.1), because both coincide with the set of tile systems that admit an infinite ribbon. Here a $T$-supertile is a connected set of positions, filled with tiles of $T$, that can be built from one tile by adding tiles one at a time, each sticking to some tile placed before, and supertiles are equivalent if they differ by a translation.

With a prescribed seed tile, the existence of an infinite ribbon or snake through it was known to be undecidable; the theorem settles the unseeded version, posed as the unlimited infinite snake problem. In a ribbon no position is visited twice, while the infinite snakes of the snake problem may cross themselves at sites carrying identical tiles; the theorem also shows that the existence of infinite non-self-crossing snakes is undecidable.

## Depends on

- [Wang tiles and valid tilings](wang-tiles-and-valid-tilings.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](the-tiling-problem-is-undecidable.md)

## Expansion

The proof constructs a directed tile system with the strong plane-filling property (Theorem 3.1): in a *directed* tile system each tile carries an arrow to a neighbor, a *directed zipper* is a ribbon following the arrows in which all adjacent tiles match, and the property forces every infinite directed zipper to cover arbitrarily large squares (Definition 2.1(ii), which the source calls plane-filling) while guaranteeing that one exists. Combining this system with a given tile set reduces the tiling problem to the existence of an infinite directed zipper (Theorem 4.1). Each directed tile is then replaced by a ribbon motif, a short ribbon entering on one side and leaving towards its arrow, whose glues force any infinite ribbon to be a sequence of motifs, so infinite directed zippers correspond to infinite ribbons (Theorem 4.2). A complete expansion links a page for the existence of a directed tile system with the strong plane-filling property (Theorem 3.1 of the source), the main construction of the proof.

## Sources

- Leonard Adleman, Jarkko Kari, Lila Kari, Dustin Reishus and Petr Sosík, "The undecidability of the infinite ribbon problem: implications for computing by self-assembly", *SIAM Journal on Computing* 38(6), pp. 2356–2381, 2009, doi:[10.1137/080723971](https://doi.org/10.1137/080723971); read in the authors' copy at <https://cs.uwaterloo.ca/~lila/pdfs/The%20Undecidability%20of%20the%20Infinite%20Ribbon%20Problem%20Implications%20for%20Computing%20by%20Self-Assembly.pdf>, which carries the journal pagination: the notation and definitions of Section 2, Theorem 3.1, Theorems 4.1 and 4.2 with their proofs and the discussion of the snake problem after them, and Definitions 5.1 and 5.2 with Theorem 5.1.
