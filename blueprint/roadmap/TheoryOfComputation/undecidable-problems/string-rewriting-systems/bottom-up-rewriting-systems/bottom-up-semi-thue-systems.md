# Bottom-up semi-Thue systems

A semi-Thue system is bottom-up with bound $k$ if every derivation can be replaced by one with the same ends in which successive rewrites
proceed from right to left in a precise sense, recorded by marks on the letters that never exceed $k$; such systems preserve regularity
under inverse rewriting.

A *semi-Thue system* over a finite alphabet $A$ is a finite set $S$ of rules $u \to v$ with $u, v \in A^*$; it is *length-increasing* if $|u| \le |v|$ for every rule, and a
derivation applies rules to factors, $xuy \to xvy$. Following the source, words are viewed as terms, the word $a_1 \cdots a_n$ being the term $a_1(a_2(\cdots a_n(\#)\cdots))$
with unary letters, so that letters further right lie deeper.

**Marked derivations.** A *marked word* attaches a natural number, its *mark*, to each letter; unmarked words have all marks $0$. A *marked step* rewrites a marked word
$\bar x \bar u \bar y$, where $\bar u$ carries the letters of $u$ for a rule $u \to v$, into $\bar x\, v\, (\bar y \odot M)$: the letters of $v$ get mark $0$, the letters of $\bar x$ keep their
marks, and every mark $m$ in the suffix $\bar y$ is replaced by $\max(m, M)$, where $M$ is one plus the largest mark among the letters of $\bar x \bar u$ (with $\max \emptyset = 0$).
A marked derivation is *weakly bottom-up* if at every step the first letter of the rewritten factor $\bar u$ has mark $0$; an ordinary derivation is weakly bottom-up if the
marked derivation starting from its unmarked first word is. For $k \ge 1$, a derivation is *$\mathrm{bu}(k)$* if it is weakly bottom-up and all marks along the corresponding
marked derivation are at most $k$, and *$\mathrm{bu}^-(k)$* if it is weakly bottom-up and the marks of the rewritten factors stay below $k$.

**Bottom-up systems.** The system $S$ is $\mathrm{BU}(k)$, respectively $\mathrm{BU}^-(k)$, if for all words $s, t$ with $s \to_S^* t$ there is a $\mathrm{bu}(k)$-derivation,
respectively a $\mathrm{bu}^-(k)$-derivation, from $s$ to $t$; it is *bottom-up* if it is $\mathrm{BU}(k)$ for some $k$. For semi-Thue systems the two notions $\mathrm{BU}(k)$ and
$\mathrm{BU}^-(k)$ coincide. Bottom-up systems include left-basic semi-Thue systems, and for every bottom-up system the set of ancestors of a regular language is regular.

## Depends on

- [Rewriting rules](../rule.md)
- [Derivations in a string rewriting system](../derives.md)

## Proof depends on

None.

## Sources

- I. Durand and G. Sénizergues, "Bottom-up rewriting for words and terms", *Journal of Symbolic Computation* 67:93–121, 2015, doi:10.1016/j.jsc.2014.06.001; read in arXiv:0903.2554v2: Section 3 (marked symbols and terms, marked rewriting, weakly bottom-up, $\mathrm{bu}(k)$ and $\mathrm{bu}^-(k)$ derivations, and bottom-up systems), Section 2 (words viewed as terms) and Section 4 (preservation of recognizability).
