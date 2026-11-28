# The Post correspondence problem is undecidable for five pairs of words

No algorithm decides, for a given list of five pairs of words, whether the list has a solution of the Post correspondence
problem.

Precisely, let $\mathrm{PCP}(5)$ be the restriction of the [Post correspondence problem](pcp.md) to instances with exactly
five pairs: given a finite alphabet $\Sigma$ and words $r_1, \dots, r_5, v_1, \dots, v_5 \in \Sigma^*$, decide whether there is a
nonempty sequence $i_1, \dots, i_\ell \in \{1, \dots, 5\}$ with

$$
r_{i_1} r_{i_2} \cdots r_{i_\ell} = v_{i_1} v_{i_2} \cdots v_{i_\ell} .
$$

Then $\mathrm{PCP}(5)$ is undecidable. The number of pairs is fixed; the words, and hence their lengths, vary. The instances
built in the proof use the alphabet $\{0, 1\}$.

This improves the earlier bound of seven pairs. The problem is decidable for two pairs (Ehrenfeucht, Karhumäki and
Rozenberg), and the source leaves the cases of three and four pairs open.

## Depends on

- [The Post correspondence problem](pcp.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for binary tag systems is undecidable](../../equivalence-of-models/tag-systems/the-halting-problem-for-binary-tag-systems-is-un.md)

## Expansion

The proof reduces the halting problem for a restricted family of binary tag systems: deletion number $\beta$, alphabet
$\{b, c\}$, rules $b \to b$ and $c \to u_0 u_1 \cdots u_l b$, started on the word $u_{\beta - 1} \cdots u_l b$. This
restricted halting problem is undecidable by the construction behind the binary tag system theorem. The symbols are encoded
as $\langle b \rangle = 1 0^\beta 1$ and $\langle c \rangle = 1$, and the instance has five pairs over $\{0, 1\}$: the pair
$(1,\ 1 \langle u_0 \rangle \cdots \langle u_l \rangle 1 0)$, which starts the match and simulates the rule for $c$, a pair
with top word $1 0^\beta 1$ that simulates the rule $b \to b$, two pairs that match an encoded $b$ or $c$ while extending a
trailing block of zeros, and the pair $(1 0^\beta 1 1 1 1,\ 1 1 1 1)$ that closes the match.

A partial match $(r, v)$ with $r$ a prefix of $v$ stores the current dataword of the tag system in the unmatched suffix of
$v$; each tag step is simulated by matching the encoded first symbol, appending the encoded rule, and matching $\beta - 1$
further symbols. A choice that leaves the simulation produces a block of zeros that cannot be matched, and the last pair
closes a match exactly when the tag system reaches the halting dataword $b$.

## Sources

- T. Neary, "Undecidability in binary tag systems and the Post correspondence problem for five pairs of words", in *32nd Symposium on Theoretical Aspects of Computer Science (STACS 2015)*, LIPIcs 30, pp. 649–661, 2015, doi:10.4230/LIPIcs.STACS.2015.649: Definition 10, Theorem 11 and its proof, Lemma 9 (the restricted tag systems), and Section 1 (earlier bounds and the decidable case of two pairs). Read in the open-access copy https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf (the published version).
