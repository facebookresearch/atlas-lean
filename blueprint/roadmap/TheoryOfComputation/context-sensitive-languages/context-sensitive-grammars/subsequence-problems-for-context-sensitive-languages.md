# Subsequence matching and analysis problems are undecidable for context-sensitive languages

For languages given by context-sensitive grammars, no algorithm decides whether some word, or every word, contains a given subsequence, nor whether some or all words are $k$-universal, nor whether the language has $m$-universal words for every $m$.

A word $w$ is a *subsequence* of $v$, written $w\le v$, if $w$ is obtained from $v$ by deleting letters. For an alphabet $\Sigma$ and $k\ge0$, a word is *$k$-universal* (with respect to $\Sigma$) if every word of $\Sigma^k$ is a subsequence of it. A grammar is *context-sensitive* if each production $p\to q$ has a left side $p$ that contains a nonterminal and satisfies $|p|\le|q|$, with no production $S\to\varepsilon$ (see [context-sensitive grammars](is-context-sensitive.md)); $L$ is the [language generated](language.md) by the given grammar.

**Theorem.** Each of the following problems is undecidable when the language $L$ is given by a context-sensitive grammar:
1. (*$\exists$-subsequence*) given $L$ and a word $w$, is there $v\in L$ with $w\le v$?
2. (*$\forall$-subsequence*) given $L$ and a word $w$, is $w\le v$ for every $v\in L$?
3. (*$\exists$-$k$-universality*) given $L$ and $k$, does $L$ contain a $k$-universal word?
4. (*$\forall$-$k$-universality*) given $L$ and $k$, is every word of $L$ $k$-universal?
5. (*$\infty$-universality*) given $L$, does $L$ contain an $m$-universal word for every $m\ge1$?

(Theorem 3 of the source, for Problems 1–5.) Here $k$-universality is taken with respect to the terminal alphabet $\Sigma$ of the given grammar, and, following the source, languages do not contain the empty word, which the definition above guarantees. Adding $\varepsilon$ to $L$ would change the answer to Problem 1 for $w = \varepsilon$ and to Problem 3 for $k = 0$ when $L$ is otherwise empty, and would make Problem 2 false unless $w = \varepsilon$ and Problem 4 false unless $k = 0$; it would not change Problem 5.

By contrast, the source shows that all five problems are decidable for context-free languages given by grammars in Chomsky normal form, as they are for regular languages.

## Depends on

- [Context-sensitive grammars](is-context-sensitive.md)
- [Language of an unrestricted grammar](language.md)
- [Chomsky normal form](../../context-free-languages/grammars-and-pushdown-automata/chomsky-normal-form/is-chomsky-normal-form.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Emptiness of a linear bounded automaton on computable input slices is undecidable](../../undecidable-problems/emptiness-problem-for-linear-bounded-automata/exists-is-lba-not-computable-pred-forall.md)

## Expansion

Each problem is reduced from emptiness of context-sensitive languages. A good expansion links a page for the effective construction, from a code $c$, of a context-sensitive grammar generating the inputs of the slice of $c$ on which the linear bounded automaton of the linked result halts (the standard simulation of a linear bounded automaton by a context-sensitive grammar); with it, the linked result makes emptiness of context-sensitive grammars undecidable.

Let $G$ generate $L\subseteq\{1,\dots,\sigma\}^*$ from the start symbol $S$. First replace every terminal $a$ in the productions of $G$ by a fresh nonterminal $X_a$ and add the productions $X_a\to a$. This keeps $L$ (a derivation can postpone every step $X_a\to a$ to its end, and terminals occur in no left side) and keeps $G$ context-sensitive, and now every left side of a production of $G$ consists of nonterminals of $G$ only, so no production of $G$ applies to a part of a sentential form that contains a symbol added below. Let $0$ be a fresh letter; each reduction adds a new start symbol $S'$ (and, for Problem 5, a new nonterminal $R$).

- Problems 1 and 2: with $S'\to\sigma S$ and $S'\to0$, the language is $\{0\}\cup\sigma L$. Some word contains $\sigma$ as a subsequence iff $L\ne\emptyset$, and every word contains $0$ iff $L=\emptyset$.
- Problem 3: with $S'\to12\cdots\sigma\,S$ only, the language is $12\cdots\sigma\,L$ over the alphabet $\{1,\dots,\sigma\}$, and it has a $1$-universal word iff $L\ne\emptyset$.
- Problem 4: with $S'\to012\cdots\sigma$ and $S'\to S$, the language is $\{012\cdots\sigma\}\cup L$, and every word is $1$-universal over $\{0,\dots,\sigma\}$ iff $L=\emptyset$, since no word of $L$ contains $0$.
- Problem 5: with $S'\to012\cdots\sigma$, $S'\to RS$ and $R\to01\cdots\sigma R\mid01\cdots\sigma$, the language is $\{012\cdots\sigma\}\cup(01\cdots\sigma)^+L$, which has $m$-universal words for all $m$ iff $L\ne\emptyset$.

The source's proof adds the new productions to $G$ directly; the replacement of terminals by nonterminals is a modification, needed because a production of $G$ with a terminal on its left side could otherwise apply across the new prefix (for instance $2S\to22$ with $L(G)=\emptyset$).

## Sources

- Szilárd Zsolt Fazekas, Tore Koß, Horst Patrick Kretschmer, Florin Manea, Robert Mercaş and Timo Specht, "Subsequence Matching and Analysis Problems for Formal Languages", *RAIRO - Theoretical Informatics and Applications* 60 (2026), article 36, doi:[10.1051/ita/2026036](https://doi.org/10.1051/ita/2026036); read in arXiv:2410.07992v1 ([arXiv](https://arxiv.org/abs/2410.07992v1)), whose numbering is used: Problems 1–5 (introduction), the definitions of Section 2 (subsequences, $k$-universality, context-sensitive grammars), Theorem 3 (Section 3) and its proof, and the decidability results for context-free languages in Sections 4–6.
