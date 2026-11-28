# Bottom-up semi-Thue systems

A semi-Thue system is bottom-up with bound $k$ if every derivation can be replaced by one with the same ends in which successive rewrites
proceed from right to left in a precise sense, recorded by marks on the letters that never exceed $k$; such systems preserve regularity
under inverse rewriting.

A *semi-Thue system* over a finite alphabet $A$ is a finite set $S$ of rules $u \to v$ with $u, v \in A^*$; it is *length-increasing* if $|u| \le |v|$ for every rule, and a
derivation applies rules to factors, $xuy \to xvy$. Following the source, words are viewed as terms, the word $a_1 \cdots a_n$ being the term $a_1(a_2(\cdots a_n(\#)\cdots))$
with unary letters, so that letters further right lie deeper.

**Marked derivations.** A *marked word* is a word $a_1 \cdots a_n$ followed by the end symbol $\#$, each of these $n + 1$ symbols carrying a natural number, its *mark*; an unmarked word $w$ is $w\#$ with all marks $0$. A *marked step* with a rule $u \to v$ rewrites a marked word $\bar x \bar u \bar z$, where $\bar u$ carries the letters of $u$ and the suffix $\bar z$ ends with the marked end symbol, into $\bar x\, v\, (\bar z \odot M)$: the letters of $v$ get mark $0$, the letters of $\bar x$ keep their marks, and every mark $m$ in $\bar z$, the mark of $\#$ included, is replaced by $\max(m, M)$, where $M$ is one plus the largest mark among the letters of $\bar x \bar u$ (with $\max \emptyset = 0$); these are equations (11)–(14) of the source for the term $a_1(\cdots a_n(\#)\cdots)$, the suffix $\bar z$ being the substituted subterm. A marked derivation is *weakly bottom-up* if every step satisfies Definition 3.7 of the source: when $u$ is nonempty, the first letter of $\bar u$ has mark $0$; when $u$ is empty, every letter of $\bar x$ has mark $0$. An ordinary derivation is weakly bottom-up if the marked derivation starting from its unmarked first word is. For $k \ge 1$, a derivation is *$\mathrm{bu}(k)$* if it is weakly bottom-up and every mark of every marked word along the corresponding marked derivation, the marks of $\#$ included, is at most $k$, and *$\mathrm{bu}^-(k)$* if it is weakly bottom-up and every mark of the rewritten factors $\bar u$ is below $k$ (Definition 3.16). For example, with the rules $a \to d$ and $db \to c$, the derivation $ab \to db \to c$ has the marked form $a\,b\,\# \to d\,b^{1}\,\#^{1} \to c\,\#^{2}$; it is weakly bottom-up, but not $\mathrm{bu}(1)$.

**Bottom-up systems.** The system $S$ is $\mathrm{BU}(k)$, respectively $\mathrm{BU}^-(k)$, if for all words $s, t$ with $s \to_S^* t$ there is a $\mathrm{bu}(k)$-derivation,
respectively a $\mathrm{bu}^-(k)$-derivation, from $s$ to $t$; it is *bottom-up* if it is $\mathrm{BU}(k)$ for some $k$. For semi-Thue systems the two notions $\mathrm{BU}(k)$ and
$\mathrm{BU}^-(k)$ coincide (the remark after Theorem 5.11 of the source). The inverse of every left-basic semi-Thue system is $\mathrm{BU}^-(1)$ (Lemma 3.22), and for every bottom-up system the set of ancestors of a regular language is regular.

## Depends on

- [Rewriting rules](../rule.md)
- [Derivations in a string rewriting system](../derives.md)

## Proof depends on

None.

## Sources

- I. Durand and G. Sénizergues, "Bottom-up rewriting for words and terms", *Journal of Symbolic Computation* 67:93–121, 2015, doi:10.1016/j.jsc.2014.06.001; read in arXiv:0903.2554v2: Section 3 (marked symbols and terms, marked rewriting, weakly bottom-up, $\mathrm{bu}(k)$ and $\mathrm{bu}^-(k)$ derivations, and bottom-up systems), Section 2 (words viewed as terms), Section 4 (preservation of recognizability) and the remark after Theorem 5.11 in Section 5.
