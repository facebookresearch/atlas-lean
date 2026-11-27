# Leftmost-longest replaceAll

The replaceAll function with a regular-expression pattern scans a subject string left to right and replaces each leftmost and longest match of the pattern by a replacement string; a pattern denoting only the empty word inserts the replacement between letters and at both ends.

Let $\Sigma$ be a finite alphabet and $e$ a regular expression over $\Sigma$, built from $\emptyset$, $\varepsilon$, letters, $+$, concatenation and $^*$, with language $L(e)$ defined inductively: $L(\emptyset) = \emptyset$, $L(\varepsilon) = \{\varepsilon\}$, $L(a) = \{a\}$, $L(e_1 + e_2) = L(e_1) \cup L(e_2)$, $L(e_1 e_2) = L(e_1) L(e_2)$ and $L(e^*) = L(e)^*$. For a word $v = v_1 u v_2$, the factor $u$ is the *leftmost and longest matching* of $e$ in $v$ if

- when $\varepsilon \notin L(e)$: $u \in L(e)$; for every strict prefix $v_1'$ of $v_1$, the word $(v_1')^{-1} v$ obtained by deleting $v_1'$ from the front of $v$ is not in $L(e \cdot \Sigma^*)$; and $u v_2' \notin L(e)$ for every nonempty prefix $v_2'$ of $v_2$;
- when $\varepsilon \in L(e)$: $u \in L(e)$, $v_1 = \varepsilon$, and $u v_2' \notin L(e)$ for every nonempty prefix $v_2'$ of $v_2$.

For words $u, v$, the word $\mathrm{replaceAll}(u, e, v)$ is defined by induction on $|u|$:

- if $u$ has no factor in $L(e)$, then $\mathrm{replaceAll}(u, e, v) = u$;
- if $\varepsilon \in L(e)$ and $u$ itself is the leftmost and longest matching of $e$ in $u$, then $\mathrm{replaceAll}(u, e, v) = v$;
- if $\varepsilon \in L(e)$, $u = u_1 a u_2$ with $a \in \Sigma$, and $u_1$ is the leftmost and longest matching of $e$ in $u$, then $\mathrm{replaceAll}(u, e, v) = v \, a \, \mathrm{replaceAll}(u_2, e, v)$;
- if $\varepsilon \notin L(e)$, $u = u_1 u_2 u_3$, and $u_2$ is the leftmost and longest matching of $e$ in $u$, then $\mathrm{replaceAll}(u, e, v) = u_1 \, v \, \mathrm{replaceAll}(u_3, e, v)$.

The arguments $u$, $e$ and $v$ are the *subject*, the *pattern* and the *replacement*. The semantics depends only on $L(e)$; in particular, which alternative of a union is tried first plays no role. For example, $\mathrm{replaceAll}(abab, ab, d) = dd$, $\mathrm{replaceAll}(baac, a^+, b) = bbc$, $\mathrm{replaceAll}(aaaa, \varepsilon, d) = dadadadad$ and $\mathrm{replaceAll}(baac, a^*, b) = bbbcb$.

## Depends on

None.

## Proof depends on

None.

## Expansion

This is a definition. The leftmost condition says that no match starts earlier; the longest condition says that the chosen match cannot be extended to the right. When $\varepsilon \in L(e)$ the match always starts at the current position: the longest prefix in $L(e)$ (possibly empty) is replaced, the next letter, if any, is copied, and the procedure recurs on the rest; for instance $\mathrm{replaceAll}(a, a^*, b) = b$, while for $L(e) = \{\varepsilon\}$ the replacement is inserted around every letter. In $\mathrm{replaceAll}(baac, a^*, b)$ the empty match before $b$, the match $aa$ and the empty match at the end are each replaced. Implementations of regular expressions in programming languages differ from this semantics, for instance in how they order alternatives and in how they treat empty matches next to nonempty ones, so results about replaceAll are relative to this fixed semantics. A semantics for greedy and lazy operators and capturing groups is given by [prioritized streaming string transducers](prioritized-streaming-string-transducers.md).

## Sources

- T. Chen, Y. Chen, M. Hague, A. W. Lin and Z. Wu, "What is decidable about string constraints with the ReplaceAll function", Proceedings of the ACM on Programming Languages 2 (POPL), Article 3, 2018, doi:[10.1145/3158091](https://doi.org/10.1145/3158091); full version arXiv:1711.03363v1, <https://arxiv.org/abs/1711.03363v1>: Definition 2.1, Section 3.1, Definition 3.1, Example 3.2, Definition 3.3 and Example 3.4.
