# The domino problem for slightly more than nm allowed n×m patterns is undecidable

Emptiness of a two-dimensional subshift of finite type given by at most $nm$ allowed $n \times m$ patterns is decidable, but with only slightly more
patterns, $nm + f(n)n$ for any unbounded computable $f$, it becomes undecidable, already over the binary alphabet.

For a rectangle $D = \{0, \dots, n-1\} \times \{0, \dots, m-1\}$ and a set $P \subseteq A^D$ of allowed $D$-patterns over a finite alphabet $A$, let

$$
\mathcal{V}(P) = \{ c \in A^{\mathbb{Z}^2} : \text{every } D\text{-pattern appearing in } c \text{ belongs to } P \}
$$

be the two-dimensional subshift of finite type of valid configurations, as for [Wang tiles](wang-tiles-and-valid-tilings.md).

**Theorem.** Let $f : \mathbb{N} \to \mathbb{N}$ be a computable function with $f \notin O(1)$.

1. For every fixed $m \ge 2$ it is undecidable, given $n$ and a set $P$ of at most $nm + f(n)n$ binary patterns of size $n \times m$, whether $\mathcal{V}(P)$ is empty.
2. It is undecidable, given $n$ and a set $P$ of at most $n^2 + f(n)n$ binary patterns of size $n \times n$, whether $\mathcal{V}(P)$ is empty.

In particular, for every $\varepsilon > 0$ it is undecidable whether a given set of at most $(1 + \varepsilon)n^2$ square $n \times n$ patterns admits a valid configuration. In
contrast, if $|P| \le nm$ then $\mathcal{V}(P)$, when nonempty, contains a periodic configuration, so its emptiness is decidable; this is the bound of Nivat's
low-complexity conjecture, which the same source settles for uniformly recurrent configurations.

## Depends on

- [Wang tiles and valid tilings](wang-tiles-and-valid-tilings.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces the domino problem for Wang tiles. A recoding theorem turns a Wang tile set $T$ into, for all large $n$, a set of at most $nm + k(n + m)$ binary
$n \times m$ patterns whose valid configurations exist exactly when $T$ tiles the plane, with constants $N$ and $k$ computable from $T$. Since $f$ is unbounded and
computable, one can search for $n \ge N$ with $f(n) \ge k + km/n$ (respectively $f(n) \ge 2k$ for squares), which gives a many-one reduction.

## Sources

- J. Kari and E. Moutot, "Decidability and periodicity of low complexity tilings", *Theory of Computing Systems* 67(1):125–148, 2023 (online 2021), doi:10.1007/s00224-021-10063-8; conference version in *STACS 2020*, LIPIcs 154, 2020, doi:10.4230/LIPIcs.STACS.2020.14. Read in arXiv:1904.01267v2: Corollaries 10 and 11 with their proofs, the recoding theorem (Theorem 9), and Corollaries 6 and 7 (periodicity and decidability below $nm$) in Section 3.
