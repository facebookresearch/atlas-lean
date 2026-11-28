# Suffix-density is undecidable for reversal-bounded counter languages

It is undecidable whether every word over the alphabet is a suffix of a word accepted by a given deterministic one-counter machine making three reversals, by a deterministic two-counter machine whose counters reverse once, or by a nondeterministic one-counter machine making one reversal.

**Theorem.** It is undecidable, given a machine accepting a language $L \subseteq \Sigma^*$ in $\mathrm{DCM}(1, 3)$, whether $L$ is [suffix-dense](prefix-suffix-and-infix-dense-languages.md), that is, whether $\mathrm{suff}(L) = \Sigma^*$. The same holds for $L$ given in $\mathrm{DCM}(2, 1)$ and for $L$ given in $\mathrm{NCM}(1, 1)$ (in the notation of [reversal-bounded counter machines](reversal-bounded-counter-machines.md)).

In contrast, suffix-density is decidable for $\mathrm{DCM}(1, 1)$, because the suffixes of such a language form a $\mathrm{DCM}$ language and inclusion is decidable for $\mathrm{DCM}$; prefix-density is decidable for all of $\mathrm{DCM}$ and for deterministic pushdown languages.

## Depends on

- [Reversal-bounded counter machines](reversal-bounded-counter-machines.md)
- [Prefix-dense, suffix-dense and infix-dense languages](prefix-suffix-and-infix-dense-languages.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

Fix a deterministic Turing machine $Z$ accepting a unary recursively enumerable but not recursive set, and an input $a^d$. Let $T$ be the regular set of words $ID_1 \# ID_2^R \# \cdots \# ID_k^R$ that start with the initial configuration on $a^d$ and end with the halting configuration, and let $L_{na} \subseteq T$ consist of those in which some $ID_{i+1}$ is not a valid successor of $ID_i$. Then $T \subseteq L_{na}$ if and only if $Z$ does not halt on $a^d$. Writing $L_{na}(p)$ for the words of $T$ with an error detectable around position $p$, the language $L' = \{\%^p u x : u \in \Sigma \Sigma_{\%}^*,\ p = |u| + p',\ x \in L_{na}(p')\} \cup \overline{\Sigma_{\%}^* T}$ (where $\Sigma_{\%} = \Sigma \cup \{\%\}$ for a new symbol $\%$) is accepted by a $\mathrm{DCM}(1, 3)$ machine, which counts the $\%$ symbols and uses the counter to locate the error, and $\mathrm{suff}(L') = \Sigma_{\%}^*$ if and only if $T \subseteq L_{na}$. Since $\mathrm{DCM}(1, 3) \subseteq \mathrm{DCM}(2, 1)$, the second case follows, and for $\mathrm{NCM}(1, 1)$ the prefix $u$ is guessed nondeterministically without using the counter.

## Sources

- J. Eremondi, O. H. Ibarra and I. McQuillan, "On the Density of Context-Free and Counter Languages", *International Journal of Foundations of Computer Science* 29(2):233–250, 2018, doi:[10.1142/S0129054118400051](https://doi.org/10.1142/S0129054118400051); numbering of arXiv:1903.03001v1: Proposition 7 (suffix-density) in Section 3 (stated for $\mathrm{DCM}(1,3)$, $\mathrm{DCM}(2,1)$ and $\mathrm{NCM}(1,1)$) with its proof, Lemmas 1 and 2 (on $Z$, $T$ and $L_{na}$) before it, and Corollary 3 (decidability for $\mathrm{DCM}(1,1)$) and Corollary 2 and Proposition 2 (prefix-density) in the same section.
