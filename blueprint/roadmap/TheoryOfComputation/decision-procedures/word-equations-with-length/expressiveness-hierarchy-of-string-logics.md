# Expressiveness of word equations with length and regular constraints

Viewing a quantifier-free formula and one of its variables as defining a language, word equations alone, with length constraints, with regular constraints, and with both form a strict hierarchy below the recursively enumerable languages; the length and regular extensions are incomparable.

Fix a sufficiently large finite alphabet $\Sigma$ of constants. Let WE be the set of quantifier-free formulas built from word equations with $\wedge$, $\vee$, $\neg$; WE + REG adds atoms $x \in L$ for regular languages $L$ (given by a regular expression, an NFA or a DFA; these are interchangeable here since only the expressed languages matter); WE + LEN adds atoms $c_0 + \sum_{i} c_i |x_i| = 0$ with $c_i \in \mathbb Z$; WE + LEN + REG allows both. Assignments map variables to possibly empty words over $\Sigma$. For a formula $\psi$ and a variable $x$ of $\psi$, the language expressed by $x$ in $\psi$ is $\{h(x) : h \text{ satisfies } \psi\}$, and $\mathcal L(T)$ denotes the class of languages expressed in this way in the logic $T$. Then, for $T \in \{\text{WE + LEN},\ \text{WE + REG}\}$,

$$\mathcal L(\text{WE}) \subsetneq \mathcal L(T) \subsetneq \mathcal L(\text{WE + LEN + REG}) \subsetneq \mathrm{RE},$$

where RE is the class of recursively enumerable languages over $\Sigma$, and $\mathcal L(\text{WE + REG})$ and $\mathcal L(\text{WE + LEN})$ are incomparable. In particular some recursively enumerable languages are not expressible in WE + LEN + REG. This strictness is a statement about expressiveness and does not by itself make satisfiability for WE + LEN + REG decidable.

## Depends on

- [Word equations with length and regular constraints](length-and-regular-constraints.md)
- [Unrestricted grammars generate exactly the recursively enumerable languages](../../context-sensitive-languages/chomsky-hierarchy/unrestricted-grammars-generate-exactly-the.md)
- [Solution of a word equation](../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)

## Proof depends on

None.

## Expansion

All expressed languages are recursively enumerable: enumerate assignments and check the formula. The non-strict inclusions hold by definition. The strict parts rest on the following results of the source.

1. *Lemma 6.* For distinct letters $a, b, c$, the regular language $\{vc : v \in \{a, b\}^*\}$ is not expressible in WE + LEN. It is expressed in WE + REG by the single atom $x \in \{a, b\}^* c$, so this shows $\mathcal L(\text{WE + REG}) \not\subseteq \mathcal L(\text{WE + LEN})$, and in particular $\mathcal L(\text{WE}) \ne \mathcal L(\text{WE + REG})$.
2. *Lemma 8.* The language $\{ucv : u, v \in \Sigma^*,\ |u| = |v|\}$, which the source notes is clearly expressible in WE + LEN (for instance by $x = ucv \wedge |u| = |v|$ with variables $u, v$), is not expressible in WE + REG. So $\mathcal L(\text{WE + LEN}) \not\subseteq \mathcal L(\text{WE + REG})$, and in particular $\mathcal L(\text{WE}) \ne \mathcal L(\text{WE + LEN})$. (The source also derives the strictness of $\mathcal L(\text{WE}) \subsetneq \mathcal L(T)$ from earlier work of Karhumäki, Mignosi and Plandowski and of Büchi and Senger.)
3. Incomparability (1 and 2) gives the strict inclusions $\mathcal L(T) \subsetneq \mathcal L(\text{WE + LEN + REG})$.
4. *Theorem 3.* Some recursively enumerable language over a six-letter alphabet is not expressible in WE + LEN + REG; the proof compares growth functions $\#_L(n)$, the number of words of length $n$ in $L$, of expressible languages with that of a specially built language.

Lemmas 6 and 8 are proved with synchronising factorisation schemes (Lemmas 5 and 7 of the source, adapted from Karhumäki, Mignosi and Plandowski). These tools are internal to the source and have no pages here. If the last inclusion were an equality, satisfiability for WE + LEN + REG would be undecidable; its strictness leaves that question open.

## Sources

- Joel D. Day, Vijay Ganesh, Nathan Grewal, Matthew Konefal and Florin Manea, "A Closer Look at the Expressive Power of Logics Based on Word Equations", *Theory of Computing Systems* 68:322–379, 2024, <https://doi.org/10.1007/s00224-023-10154-8>, Definitions 1–5 (the logics and expressibility; Definition 2 allows any usual representation of regular languages), Remark 1 (sufficiently large alphabet), Lemmas 5 and 7 (synchronising factorisation schemes), Lemma 6, Lemma 8, Theorem 3 (a recursively enumerable language not expressible in WE + LEN + REG, via growth functions), Theorem 4 (the hierarchy and incomparability), and Section 1 (consequences for decidability).
