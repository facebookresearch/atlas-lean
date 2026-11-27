# Mortality is undecidable for six 3 × 3 or two 18 × 18 integer matrices

The mortality problem stays undecidable when the instance is restricted to exactly six $3 \times 3$ integer matrices, and when
it is restricted to exactly two $18 \times 18$ integer matrices.

Precisely, each of the following problems is undecidable:

1. given six matrices $M_1, \dots, M_6 \in \mathbb{Z}^{3 \times 3}$, decide whether some product $M_{i_1} \cdots M_{i_\ell}$
   with $\ell \ge 1$ equals the zero matrix;
2. given two matrices $M_1, M_2 \in \mathbb{Z}^{18 \times 18}$, decide the same question.

Both the dimension and the number of matrices are fixed; only the entries vary. These bounds improve the earlier bounds of
seven $3 \times 3$ matrices and two $21 \times 21$ matrices.

## Depends on

- [The matrix mortality problem](the-matrix-mortality-problem.md)

## Proof depends on

- [The Post correspondence problem is undecidable for five pairs of words](../../post-correspondence-problem/the-post-correspondence-problem-is-undecidable-f.md)

## Expansion

The source obtains both bounds by feeding its new bound for the Post correspondence problem, five pairs of words, into
earlier reductions from the Post correspondence problem to mortality: the reduction of Halava and Harju to $3 \times 3$
integer matrices gives the first bound, and the reduction of Cassaigne and Karhumäki to two matrices of larger dimension gives
the second. The earlier bounds, seven $3 \times 3$ matrices and two $21 \times 21$ matrices, are due to Halava, Harju and
Hirvensalo, who started from the earlier bound of seven pairs of words.

## Sources

- T. Neary, "Undecidability in binary tag systems and the Post correspondence problem for five pairs of words", in *32nd Symposium on Theoretical Aspects of Computer Science (STACS 2015)*, LIPIcs 30, pp. 649–661, 2015, doi:10.4230/LIPIcs.STACS.2015.649: Corollary 12 and the paragraph before it. Read in the open-access copy https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf (the published version).
