# The infinite Post correspondence problem is undecidable for instances of size 9

No algorithm decides, for two morphisms on a nine-letter domain alphabet, whether they agree on some infinite word.

Precisely, the [infinite Post correspondence problem](the-infinite-post-correspondence-problem.md) restricted to instances
$(h, g)$ with $h, g : A^* \to B^*$ and $|A| = 9$ is undecidable. The size of the domain alphabet is fixed at $9$; in the
instances built by the proof the target alphabet $B$ has four letters.

The problem is undecidable in general (Ruohonen), was known to be undecidable for size $105$ (Blondel and Canterini), and is
decidable for binary instances, $|A| = 2$. The source states that the cases $3 \le |A| \le 8$ are open; Dong and Liu later announced undecidability for instances of size $8$ ("Undecidability of infinite Post correspondence problem for instances of size 8", RAIRO – Theoretical Informatics and Applications 46(3):451–457, 2012, doi:10.1051/ita/2012015; not read here, cited from its title).

## Depends on

- [The infinite Post correspondence problem](the-infinite-post-correspondence-problem.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof starts from a theorem of Matiyasevich and Sénizergues: there is a semi-Thue system with three rules whose
termination problem is undecidable, that is, no algorithm decides for an input word $u$ whether every derivation from $u$ is
finite. Recode the system over the binary alphabet $\{a, b\}$. For a semi-Thue system $T$ with $n$ rules and an input word
$u$, the proof builds morphisms on the domain $A = \{a_1, a_2, b_1, b_2, d, \#\} \cup R$, where $R$ holds one letter per rule,
into $\{a, b, d, \#\}^*$, using desynchronizing morphisms that interleave the letter $d$. Every infinite solution then has the
form $d w_1 \# w_2 \# \cdots$ with exactly one rule letter in each $w_j$, and the images of consecutive blocks spell
consecutive words of a derivation $u = u_1 \to u_2 \to \cdots$ of $T$. Hence $(h, g)$ has an infinite solution if and only if
$T$ has an infinite derivation from $u$, and the size of the instance is $n + 6 = 9$.

## Sources

- V. Halava and T. Harju, "Undecidability of infinite Post correspondence problem for instances of size 9", *RAIRO – Theoretical Informatics and Applications* 40(4):551–557, 2006, doi:10.1051/ita:2006039: Corollary 2, Lemma 2 and its proof, Theorem 1 (the result of Matiyasevich and Sénizergues) and Section 1 (earlier bounds and the binary case). Read in the open-access copy https://www.numdam.org/item/10.1051/ita:2006039.pdf (the published version).
