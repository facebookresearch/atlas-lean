# The infinite Post correspondence problem

The *infinite Post correspondence problem* asks, for two morphisms $h, g$ of free monoids, whether some infinite word $\omega$
satisfies $h(\omega) = g(\omega)$, meaning that $h$ and $g$ agree on every finite prefix up to comparability.

Let $A$ and $B$ be finite alphabets. An *instance* is a pair $(h, g)$ of morphisms $h, g : A^* \to B^*$, and its *size* is
$|A|$, the cardinality of the domain alphabet. A *solution* in the sense of the [Post correspondence problem](pcp.md) is a
nonempty word $w \in A^+$ with $h(w) = g(w)$. Two finite words are *comparable* if one is a prefix of the other. An *infinite
solution* of $(h, g)$ is an infinite word $\omega = a_1 a_2 \cdots \in A^\omega$ such that $h(u)$ and $g(u)$ are comparable for
every finite prefix $u$ of $\omega$; one then writes $h(\omega) = g(\omega)$.

The *infinite Post correspondence problem* ($\omega\mathrm{PCP}$) is the decision problem: given an instance $(h, g)$, does it
have an infinite solution? An infinite word is *ultimately periodic* if it equals $u v v v \cdots$ for finite words $u$ and
$v$ with $v$ nonempty.

The instances are those of the Post correspondence problem written as pairs of morphisms: the list of pairs
$(h(a), g(a))$, $a \in A$, is a list of $|A|$ dominoes, and the size of the instance is the number of dominoes.

## Depends on

- [The Post correspondence problem](pcp.md)

## Proof depends on

None.

## Sources

- V. Halava and T. Harju, "Undecidability of infinite Post correspondence problem for instances of size 9", *RAIRO – Theoretical Informatics and Applications* 40(4):551–557, 2006, doi:10.1051/ita:2006039: Section 1 (instances, size, comparable words, infinite solutions, ultimately periodic words). Read in the open-access copy https://www.numdam.org/item/10.1051/ita:2006039.pdf (the published version).
