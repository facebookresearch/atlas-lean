# Whether a two-tape automaton accepts a word paired with a cyclic shift is undecidable

For a finite automaton reading pairs of letters, it is undecidable whether it accepts some word of the form $xc^n \times c^n x$, or some pair of conjugate words, although whether a deterministic automaton accepts two distinct conjugates is decidable.

**Theorem.** For words $w = a_1 \cdots a_n$ and $x = b_1 \cdots b_n$ of the same length, let $w \times x = [a_1, b_1] \cdots [a_n, b_n]$ be the word over pairs of letters. Words $x, y$ are *conjugate* if $x = uv$ and $y = vu$ for some words $u, v$. Then:

1. (ACCEPTS-SHIFT) there is no algorithm that decides, given an alphabet $\Gamma$, a letter $c \notin \Gamma$ and a finite automaton $M$ over the alphabet $(\Gamma \cup \{c\})^2$, whether $M$ accepts a word $xc^n \times c^n x$ for some $x \in \Gamma^*$ and $n \ge 0$ (Theorem 2 of the source);
2. (ACCEPTS-GENERAL-SHIFT) there is no algorithm that decides, given a finite automaton $M$ over an alphabet $\Sigma^2$, whether $M$ accepts $x \times y$ for some conjugates $x, y \in \Sigma^*$ (Theorem 7).

Under the extra requirement $n \ge |x|$ the first problem becomes decidable in cubic time (Theorem 4), and whether a deterministic finite automaton accepts two distinct conjugates $uv \ne vu$ is decidable (Theorem 8). As a consequence, it is undecidable whether a $k$-automatic set of rationals contains a power of $k$ (Theorems 5 and 6); see [the companion page](whether-a-k-automatic-set-of-rationals-contains.md), which also fixes the conventions on denominators and exponents. As inputs, finite automata are given as [encoded NFAs](../../../decision-procedures/encoded-finite-automata/encoded-nfa.md), as on that page.

## Depends on

- [Encoded NFA](../../../decision-procedures/encoded-finite-automata/encoded-nfa.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof of part 1 reduces REWRITE-POWER: given length-preserving string rewriting rules over an alphabet $\Sigma$ with letters $a, b$, is there $n \ge 1$ with $a^n \Rightarrow^* b^n$? Its undecidability comes from simulating Turing machines with length-preserving rewriting (Lemma 1). For $\Gamma = \Sigma \cup \{d\}$, a regular language over pairs is built from the identity pairs $[e, e]$, $e \in \Sigma$, the pairs $[r, \ell]$ for rules $\ell \to r$ written letter by letter, and delimiters $d$ and $c$; a word $xc^n \times c^n x$ in it is forced, by the shift of $x$ by $n$ positions, to spell a rewriting sequence $a^m \Rightarrow \cdots \Rightarrow b^m$ in which each block is the rewriting of the previous one. Part 2 reduces part 1 by modifying the automaton so that, among pairs of conjugates, it can only accept pairs of the shifted form (Theorem 7). A good expansion links a page for the undecidability of REWRITE-POWER (Lemma 1 of the source), proved by simulating Turing machines on the blank tape with length-preserving rewriting.

## Sources

- J. Endrullis, J. Shallit and T. Smith, "Undecidability and Finite Automata", in *Developments in Language Theory (DLT 2017)*, Lecture Notes in Computer Science 10396, Springer, 2017, pp. 160–172, doi:[10.1007/978-3-319-62809-7_11](https://doi.org/10.1007/978-3-319-62809-7_11); read as arXiv:1702.01394v2, whose numbering is used here: Lemma 1, Theorems 2, 4, 5, 6, 7 and 8.
