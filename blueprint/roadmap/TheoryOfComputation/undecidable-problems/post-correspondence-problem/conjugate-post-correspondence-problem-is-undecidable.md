# The conjugate Post correspondence problem is undecidable

No algorithm decides, given two morphisms between free monoids, whether some nonempty word has images that are conjugate words, that is, cyclic shifts of each other; the same holds for the (2,2)-permutational variant, which allows also cyclically shifting the preimage.

Two words $x, y$ are *conjugate* if $x = uv$ and $y = vu$ for some words $u, v$. For words $u, v$ and $m \ge 1$ write $u \sim_m v$ if $u = u_1 \cdots u_m$ and $v = u_{\tau(1)} \cdots u_{\tau(m)}$ for some words $u_1, \dots, u_m$ and a permutation $\tau$ of $\{1, \dots, m\}$; so $u \sim_2 v$ says that $u$ and $v$ are conjugate.

**Problems.** Let $A$ and $B$ be finite alphabets. The *conjugate Post correspondence problem* asks, given morphisms $h, g : A^* \to B^*$, whether there is a word $w \in A^+$ such that $h(w)$ and $g(w)$ are conjugate, that is, $h(w) = uv$ and $g(w) = vu$ for some $u, v \in B^*$. The *$(m, n)$-permutational Post correspondence problem* asks whether there are nonempty words $u, v \in A^+$ with $u \sim_m v$ and $g(u) \sim_n h(v)$; the conjugate problem is the $(1,2)$-permutational one. The source's Problem 4 writes $u, v \in A^*$, but the empty words would then always be a solution, so nonempty words are meant, as in its conjugate problem.

**Theorem (Finkel, Halava, Harju and Sahla).** The conjugate Post correspondence problem is undecidable (Theorem 1 of the source). Since an instance has a solution of the $(1,2)$-permutational problem if and only if it has one of the $(2,2)$-permutational problem (Lemma 1), the $(2,2)$-permutational Post correspondence problem is undecidable as well.

Ruohonen proved undecidability of the $(m, n)$-permutational problems by simulating linearly bounded automata; the source gives a new proof of the conjugate case, noting that it was not stated explicitly in Ruohonen's earlier paper.

## Depends on

- [The Post correspondence problem](pcp.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The proof reduces the halting problem of a deterministic Turing machine on the empty tape. A semi-Thue system with end markers simulates the machine (Huet and Lankford); adding letter-by-letter cancellation rules and a rule from the halting word back to the initial word gives a system with an undecidable circular word problem, whether some word derives itself in at least one step. The source doubles the alphabet with an overlined copy, replaces the restart rule by two rules switching between the copies, and builds morphisms $h, g$ whose conjugate solutions correspond to such cyclic derivations, using desynchronizing letters and border markers. A good expansion links a page for the circular word problem of these special semi-Thue systems.

## Sources

- O. Finkel, V. Halava, T. Harju and E. Sahla, "On bi-infinite and conjugate post correspondence problems", RAIRO – Theoretical Informatics and Applications 57 (2023), article 7, https://doi.org/10.1051/ita/2023008; read in arXiv:2111.04484v3 (Problems 3 and 4, Lemma 1 and Theorem 1 of arXiv:2111.04484v3, Section 2).
- K. Ruohonen, "On some variants of Post's correspondence problem", Acta Informatica 19 (1983), no. 4, 357–367, https://doi.org/10.1007/BF00290732 (cited after the paper above, which describes its results).
