# Simple connectivity of finite 2-complexes is undecidable

There is no algorithm that decides whether a given finite $2$-dimensional simplicial complex is simply connected, because every finite group presentation is realized as the fundamental group of an effectively constructible $2$-complex and triviality of finite presentations is undecidable.

A finite simplicial complex is given by its vertex set and its list of simplices. A path-connected space is *simply connected* if its fundamental group is trivial.

**Theorem.** There is no algorithm that takes as input a finite connected simplicial complex $K$ of dimension at most $2$ and decides whether $|K|$ is simply connected. Consequently no algorithm decides simple connectivity of finite simplicial complexes of any dimension.

Conventions: the input complexes are finite and connected (connectedness is decidable from the complex). The analogous problem for contractibility of $2$-complexes is related to the triviality problem for balanced presentations, whose decidability is open.

## Depends on

- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Rabin and Adian proved that no algorithm decides, given a finite presentation $\langle g_1, \dots, g_k \mid r_1, \dots, r_l \rangle$, whether the group it presents is trivial. From such a presentation one effectively builds the presentation complex: one vertex, one edge for each generator and one $2$-cell for each relator, attached along the corresponding word; after barycentric subdivision this is a finite simplicial $2$-complex whose fundamental group is the presented group, by van Kampen's theorem. An algorithm deciding simple connectivity of finite $2$-complexes would therefore decide triviality of finite presentations. A good expansion links the undecidability of triviality, the presentation complex and van Kampen's theorem, which have no pages here.

## Sources

- Bjorn Poonen, *Undecidable problems: a sampler*, in: Interpreting Gödel: Critical Essays (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, https://doi.org/10.1017/CBO9780511756306.015, read in the copy arXiv:1204.0299v2, where the undecidability of the triviality problem is Corollary 6.3 (after the Adian–Rabin theorem, Theorem 6.2).
- Fedor Manin and Shmuel Weinberger, *Algorithmic aspects of immersibility and embeddability*, Int. Math. Res. Not. IMRN 2024, no. 17, 12433–12454, https://doi.org/10.1093/imrn/rnae170, read in the copy arXiv:1812.09413v4, whose subsection "Methods" of the introduction states that whether a given simplicial complex is simply connected is undecidable, as a consequence of Novikov's theorem on the triviality problem.
- Ulrich Bauer, Abhishek Rathod and Jonathan Spreer, *Parametrized complexity of expansion height*, in: 27th Annual European Symposium on Algorithms (ESA 2019), LIPIcs 144, Schloss Dagstuhl, 2019, article 13, https://doi.org/10.4230/LIPIcs.ESA.2019.13, read in the copy arXiv:1910.09228v1, whose introduction states the undecidability for $2$-complexes and the open status of contractibility.
- Michael O. Rabin, *Recursive unsolvability of group theoretic problems*, Ann. of Math. (2) 67 (1958), no. 1, 172–194, https://doi.org/10.2307/1969933, the original source of the undecidability of triviality, cited beside the copies read above.
