# Regular, length and string-to-number constraints over binary strings

The existential theory of binary strings with regular-membership predicates, string equality, the length function, the value of a string read as a binary numeral, and linear arithmetic over the naturals is decidable in EXPSPACE, by reduction to the existential theory of Semënov arithmetic with regular predicates.

Let $\Sigma = \{0, 1\}$. For $u = u_n u_{n-1} \cdots u_0 \in \Sigma^*$ let $[\![u]\!] = \sum_{i=0}^n 2^i u_i$, its value in binary, most significant digit first; leading zeros are allowed, so $[\![\cdot]\!]$ maps $\Sigma^*$ onto $\mathbb{N}$ but not injectively, and $[\![\varepsilon]\!] = 0$. Consider the two-sorted structure

$$
\langle \Sigma^*, \mathbb{N};\ \{w\}_{w \in \Sigma^*},\ \mathrm{len},\ \mathrm{sn},\ \{R_i\}_{i \in \mathbb{N}},\ 0, 1, + \rangle,
$$

where $\mathrm{len}(w) = |w|$, $\mathrm{sn}(u) = [\![u]\!]$, and $R_0, R_1, \dots$ enumerate the regular languages over $\Sigma$. The theory $T^{\mathrm{RE}}_{\mathrm{ln}}$ is the first-order theory of this structure without string concatenation. Its *existential fragment* consists of existentially quantified Boolean combinations of string equations $s = t$ between string variables and constants, memberships $R(s)$, and linear constraints with binary integer constants over integer terms built from integer variables, $\mathrm{len}(s)$ and $\mathrm{sn}(s)$. A regular language is given by a deterministic finite automaton and contributes the number of states of its minimal automaton to the size.

1. The existential fragment of $T^{\mathrm{RE}}_{\mathrm{ln}}$ is decidable in [EXPSPACE](../../complexity-classes/time-and-space-complexity-classes/expspace.md).
2. The existential fragment of *generalised Semënov arithmetic*, the theory of $\langle \mathbb{N}, 0, 1, +, 2^{(\cdot)}, \{R\} \rangle$, is decidable in EXPSPACE. Here $2^{(\cdot)}$ is the relation $\{(a, 2^a)\}$, and each predicate $R$, of some arity $k$, is given by a regular language $L \subseteq (\{0, 1\}^k)^*$ of synchronized $k$-tuples of binary numerals (most significant digit first, shorter numerals padded by the all-zero letter), and holds of the tuples of numbers that are values of words of $0^* L$; regular atoms occur only positively.

The source gives no lower bound beyond the PSPACE-hardness of generalised Semënov arithmetic, which expresses emptiness of intersections of deterministic automata. The full first-order theory of generalised Semënov arithmetic is undecidable, and smallest solutions of its existential formulas can have non-elementary bit-length. Adding concatenation to the string theory makes its existential fragment undecidable (a result of Berzish, Day, Ganesh, Kulczynski, Manea, Mora and Nowotka, cited by the source). Neither part concerns decimal conversion or the failure conventions of string-to-integer functions in solvers.

## Depends on

- [The class EXPSPACE](../../complexity-classes/time-and-space-complexity-classes/expspace.md)

## Proof depends on

- [Savitch's theorem](../../complexity-classes/savitch.md)

## Expansion

This node still needs its proof broken down; the source proof has these parts.

Part 1 reduces to part 2 in logarithmic space (Theorem 15, Appendix A.4, Lemma 19). In a quantifier-free formula all atoms may be assumed positive except string equations, after complementing deterministic automata and negating linear constraints. Map each string $s$ to the positive number $[\![1 s]\!]$, so that distinct strings, including those with leading zeros, stay distinct. Then $R(s)$ becomes the regular predicate given by $0^* 1 R$, string equations stay equations of numbers, $\mathrm{len}(s) = x$ becomes $2^x \le s < 2^{x+1}$, and $\mathrm{sn}(s) = x$ becomes $\exists y.\ 2^y \le s < 2^{y+1} \wedge x = s - 2^y$; every string variable is required to be positive.

Sizes on the arithmetic side are as in the source: binary encoding of numbers, and for a regular atom the number of states of the canonical minimal deterministic automaton. Part 2 (Theorem 1, Sections 3–5). A positive conjunctive formula is translated into a restricted labelled affine vector addition system with states whose language encodes its solutions (Lemma 8): the solutions of linear equations form a zero-closed regular language recognized by a deterministic automaton of exponential size (Lemma 4); each equation $x_i = 2^{y_i}$ is handled by a pair of counters, the first incremented at every step once nonzero and the second updated by $x \mapsto 2x$ and $x \mapsto 2x + 1$, accepted when the two are equal (Definition 5, Lemma 6); and these systems are closed under union, intersection, projection and inverse projection (Proposition 7). Emptiness of a restricted system with $2d$ counters is decided in nondeterministic space $|V| \cdot 2^{O(d)}$ (Proposition 9), through witnessing certificates, bounded abstract runs with residues and pumpable loops, whose existence is equivalent to nonemptiness (Theorem 11, Propositions 12–13); Savitch's theorem gives deterministic exponential space.

## Sources

- A. Draghici, C. Haase and F. Manea, "Semënov arithmetic, affine VASS, and string constraints", 41st International Symposium on Theoretical Aspects of Computer Science (STACS 2024), LIPIcs 289, Article 29, 2024, doi:[10.4230/LIPIcs.STACS.2024.29](https://doi.org/10.4230/LIPIcs.STACS.2024.29); arXiv:2306.14593v1, <https://arxiv.org/abs/2306.14593v1>: numbering of the published version, Section 1 (non-elementary smallest solutions), Sections 2.2–2.3 (numerals, generalised Semënov arithmetic, sizes, Theorem 1, undecidability of the full theory), Section 3 (Lemma 4, Definition 5, Lemmas 6 and 8, Propositions 7 and 9), Sections 4–5 (Theorem 11, Propositions 12–13), Section 6 (the theory $T_{\mathrm{lnc}}$, its fragment $T^{\mathrm{RE}}_{\mathrm{ln}}$, Theorem 15) and Appendix A.4 (the translation and Lemma 19).
