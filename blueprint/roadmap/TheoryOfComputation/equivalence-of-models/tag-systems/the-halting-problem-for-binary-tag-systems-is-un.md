# The halting problem for binary tag systems is undecidable

No algorithm decides, for a tag system over a two-letter alphabet and an initial word, whether the tag system halts.

A tag system $T$, as in [tag systems and cyclic tag systems](tag-systems-and-cyclic-tag-systems.md), has a finite alphabet
$\Sigma$, a rule $a \to \alpha(a)$ with $\alpha(a) \in \Sigma^*$ for each $a \in \Sigma$, and a deletion number $\beta \ge 2$. On a dataword
$w = w_0 w_1 \cdots w_{|w|-1}$ with $|w| \ge \beta$ one step deletes the first $\beta$ symbols and appends the word $\alpha(w_0)$ of the first symbol:

$$
w_0 w_1 \cdots w_{\beta - 1} w_\beta \cdots w_{|w|-1} \ \vdash\ w_\beta \cdots w_{|w|-1}\, \alpha(w_0) .
$$

The tag system halts on $w$ if $w \vdash^* w'$ for some dataword with $|w'| < \beta$. The *halting problem for binary tag
systems* is: given a tag system with $|\Sigma| = 2$, its deletion number $\beta$ and a dataword $w$, decide whether it halts on
$w$.

**Theorem.** The halting problem for binary tag systems is undecidable.

The alphabet size is fixed at $2$, the minimum possible; the deletion number is part of the input. With two symbols there
are only two rules, and in the construction one of them is the trivial rule $b \to b$.

## Depends on

- [Tag systems and cyclic tag systems](tag-systems-and-cyclic-tag-systems.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Cyclic tag systems emulate tag systems](cyclic-tag-systems-emulate-tag-systems.md)

## Expansion

The proof constructs, for every cyclic tag system $C$, a binary tag system $T_C$ with alphabet $\{b, c\}$ that simulates $C$:
each symbol of the cyclic tag system's dataword is encoded by a block of $b$'s and $c$'s, and the appendant of $C$ that is
currently marked is encoded by the shift, modulo $\beta$, with which the next block is entered. The simulation produces
garbage blocks that grow exponentially, so the overhead in time is exponential. Taking for $C$ a cyclic tag system that
simulates an arbitrary Turing machine and appends a distinguished appendant exactly when the machine halts, and modifying
$T_C$ to halt when that appendant appears, yields a binary tag system that halts if and only if the simulated Turing machine
halts.

## Sources

- T. Neary, "Undecidability in binary tag systems and the Post correspondence problem for five pairs of words", in *32nd Symposium on Theoretical Aspects of Computer Science (STACS 2015)*, LIPIcs 30, pp. 649–661, 2015, doi:10.4230/LIPIcs.STACS.2015.649: Definition 1 (tag systems), Definition 5, Theorem 6, Lemma 9, and Section 3. Read in the open-access copy https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf (the published version).
