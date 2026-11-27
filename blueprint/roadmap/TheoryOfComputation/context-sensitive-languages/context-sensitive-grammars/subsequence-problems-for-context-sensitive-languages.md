# Subsequence matching and analysis problems are undecidable for context-sensitive languages

For languages given by context-sensitive grammars, no algorithm decides whether some word, or every word, contains a given subsequence, nor whether some or all words are $k$-universal, nor whether the language has $m$-universal words for every $m$.

A word $w$ is a *subsequence* of $v$, written $w\le v$, if $w$ is obtained from $v$ by deleting letters. For an alphabet $\Sigma$ and $k\ge0$, a word is *$k$-universal* (with respect to $\Sigma$) if every word of $\Sigma^k$ is a subsequence of it. A grammar is *context-sensitive* if each production $p\to q$ has $|p|\le|q|$ (see [context-sensitive grammars](is-context-sensitive.md)).

**Theorem.** Each of the following problems is undecidable when the language $L$ is given by a context-sensitive grammar:
1. (*$\exists$-subsequence*) given $L$ and a word $w$, is there $v\in L$ with $w\le v$?
2. (*$\forall$-subsequence*) given $L$ and a word $w$, is $w\le v$ for every $v\in L$?
3. (*$\exists$-$k$-universality*) given $L$ and $k$, does $L$ contain a $k$-universal word?
4. (*$\forall$-$k$-universality*) given $L$ and $k$, is every word of $L$ $k$-universal?
5. (*$\infty$-universality*) given $L$, does $L$ contain an $m$-universal word for every $m\ge1$?

By contrast, the source shows that all five problems are decidable for context-free languages given by grammars in Chomsky normal form, as they are for regular languages.

## Depends on

- [Context-sensitive grammars](is-context-sensitive.md)

## Proof depends on

- [Emptiness of a linear bounded automaton on computable input slices is undecidable](../../undecidable-problems/emptiness-problem-for-linear-bounded-automata/exists-is-lba-not-computable-pred-forall.md)

## Expansion

Each problem is reduced from emptiness of context-sensitive languages, undecidable since context-sensitive grammars and linear bounded automata accept the same languages. Let $G$ generate $L\subseteq\{1,\dots,\sigma\}^*$ from the start symbol $S$, and let $0$ be a fresh letter; each reduction adds a new start symbol $S'$. With $S'\to\sigma S$ and $S'\to0$, some word contains $\sigma$ as a subsequence iff $L\ne\emptyset$, and every word contains $0$ iff $L=\emptyset$ (problems 1 and 2). With $S'\to12\cdots\sigma\,S$, the new language has a $1$-universal word iff $L\ne\emptyset$ (problem 3). With $S'\to012\cdots\sigma$ and $S'\to S$, every word is $1$-universal over $\{0,\dots,\sigma\}$ iff $L=\emptyset$ (problem 4). With $S'\to012\cdots\sigma$, $S'\to RS$ and $R\to01\cdots\sigma R\mid01\cdots\sigma$, there are $m$-universal words for all $m$ iff $L\ne\emptyset$ (problem 5).

## Sources

- Szilárd Zsolt Fazekas, Tore Koß, Horst Patrick Kretschmer, Florin Manea, Robert Mercaş and Timo Specht, "Subsequence Matching and Analysis Problems for Formal Languages", *RAIRO - Theoretical Informatics and Applications* 60 (2026), article 36, doi:[10.1051/ita/2026036](https://doi.org/10.1051/ita/2026036); read in arXiv:2410.07992v1 ([arXiv](https://arxiv.org/abs/2410.07992v1)), whose numbering is used: Problems 1–5 (introduction), the definitions of Section 2 (subsequences, $k$-universality, context-sensitive grammars), Theorem 3 (Section 3) and its proof, and the decidability results for context-free languages in Sections 4–6.
