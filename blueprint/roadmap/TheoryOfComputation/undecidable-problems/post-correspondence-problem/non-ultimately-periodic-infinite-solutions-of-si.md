# Non-ultimately periodic infinite solutions of size-6 PCP instances are undecidable

No algorithm decides, for an instance of the Post correspondence problem with six letters in its domain alphabet, whether it
has an infinite solution that is not ultimately periodic.

Precisely: given morphisms $h, g : A^* \to B^*$ with $|A| = 6$, it is undecidable whether there is an infinite word
$\omega \in A^\omega$ that is not ultimately periodic and is an infinite solution of $(h, g)$, in the sense of the
[infinite Post correspondence problem](the-infinite-post-correspondence-problem.md): $h(u)$ and $g(u)$ are comparable for
every finite prefix $u$ of $\omega$.

The restriction to non-ultimately periodic solutions matters: the instances of the reduction always have trivial
ultimately periodic infinite solutions, so the same instances say nothing about the plain infinite Post correspondence
problem, which needs three more domain letters in the
[size-9 result](the-infinite-post-correspondence-problem-is-unde.md).

## Depends on

- [The infinite Post correspondence problem](the-infinite-post-correspondence-problem.md)

## Proof depends on

None.

## Expansion

Claus's construction turns a semi-Thue system $T = (\{a, b\}, R)$ with $n$ rules and an input word $u$ into an instance of
size $n + 3$ on the domain $\{a, b, d\} \cup R$. An infinite derivation $u = w_1 \to w_2 \to \cdots$ gives an infinite
solution; inserting before the $j$-th step $j$ copies of a block that encodes the current word $w_j$ unchanged turns it into
one that is not ultimately periodic, since these blocks contain no rule letters.
Conversely, a non-ultimately periodic infinite solution must apply a rule infinitely often and so encodes an infinite
derivation. With the three-rule semi-Thue system of Matiyasevich and Sénizergues, whose termination problem is undecidable,
this gives instances of size $3 + 3 = 6$.

## Sources

- V. Halava and T. Harju, "Undecidability of infinite Post correspondence problem for instances of size 9", *RAIRO – Theoretical Informatics and Applications* 40(4):551–557, 2006, doi:10.1051/ita:2006039: Corollary 1, Lemma 1 and its proof, Theorem 1 (the result of Matiyasevich and Sénizergues). Read in the open-access copy https://www.numdam.org/item/10.1051/ita:2006039.pdf (the published version).
