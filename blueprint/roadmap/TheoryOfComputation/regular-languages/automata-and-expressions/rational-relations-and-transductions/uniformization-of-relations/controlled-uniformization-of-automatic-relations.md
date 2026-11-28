# Uniformization of automatic relations by controlled subsequential transducers is undecidable

Given an automatic relation and a regular control language prescribing how input reading and output writing may interleave, it is undecidable whether the relation has a uniformization by a subsequential transducer obeying that control language.

**Theorem.** Let $\Sigma$ (input) and $\Gamma$ (output) be disjoint alphabets. A word $w \in (\Sigma \cup \Gamma)^*$ is a *synchronization* of the pair $(u, v)$ obtained by projecting $w$ to $\Sigma$ and to $\Gamma$; a language $S \subseteq (\Sigma \cup \Gamma)^*$ defines the relation $[\![S]\!]$ of the pairs it synchronizes. A relation $R \subseteq \Sigma^* \times \Gamma^*$ is *automatic* (synchronous rational) if $R = [\![S]\!]$ for a regular $S \subseteq (\Sigma\Gamma)^*(\Sigma^* + \Gamma^*)$, and a *uniformization* of $R$ is a function $f : \mathrm{dom}(R) \to \Gamma^*$ with $(u, f(u)) \in R$ for all $u \in \mathrm{dom}(R)$. A *regular control language* is a regular $L \subseteq \{1, 2\}^*$, read as the synchronization language obtained by replacing $1$ with $\Sigma$ and $2$ with $\Gamma$; for a subsequential transducer $T$ (deterministic on its input) with final output $f(p)$ at each final state $p$, its *synchronization language* $S(T)$ consists of the words $u_1 v_1 u_2 v_2 \cdots u_n v_n f(p_n)$ for the accepting runs $(q_0, u_1, v_1, p_1) \cdots (p_{n-1}, u_n, v_n, p_n)$, which start in the initial state $q_0$ and end in a final state $p_n$, and $T$ is *$L$-controlled* if $S(T)$ is contained in that language: for every accepting run, the interleaving of its input reads and output writes, followed by the final output of its last state, belongs to it. There is no algorithm that decides, given an automatic relation $R$ and a regular control language $L$, whether $R$ has a uniformization by an $L$-controlled subsequential transducer (Theorem 14 of the source). The same holds with $L$ replaced by a regular synchronization language $S \subseteq (\Sigma \cup \Gamma)^*$ (Corollary 15).

For rational relations, already the fixed control by $(\Sigma\Gamma)^*(\Sigma^* + \Gamma^*)$ is undecidable: whether a rational relation has a uniformization by a synchronous subsequential transducer, or by a subsequential transducer with finite shiftlag, is undecidable (Corollaries 12 and 13, from a construction of Carayol and Löding). Whether an automatic relation has a uniformization by a subsequential transducer is decidable (Carayol and Löding, Theorem 18, recalled in Section 1 of the source), and so is the version with a subsequential transducer of finite shiftlag (Theorem 8), and so is whether a rational relation has one by a recognizable relation (Theorem 9).

## Depends on

- [Rational relations and transducers](../rational-relations-and-transducers.md)
- [Sequential and subsequential functions](../sequential-and-subsequential-functions.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof reduces the halting problem of a Turing machine $M$ on the empty input. Writing $\natural$ for the separator symbol of the source, the domain of the automatic relation $R_M$ consists of the words $\natural c_1 \natural \cdots \natural c_m \#$ in which $c_1, \dots, c_{m-1}$ are configurations of $M$ and $c_m$ is a prefix of one, and the control language $L_M$ lets a subsequential transducer output $\mathrm{succ}(c_i)$ while reading $c_i$, each letter of the successor being determined by a window of four input letters. $R_M$ is defined so that a pair $(u, v)$ belongs to it, for $v$ beginning with $\natural \vdash q_0 \natural\, \mathrm{succ}(c_1) \natural \cdots \natural\, \mathrm{succ}(c_{m-1})$, iff $c_1 \natural \cdots \natural c_m$ is not a halting computation of $M$; so the transducer that writes successor configurations is a uniformizer iff $M$ does not halt; the proof shows that this is the case exactly for the relation to have an $L_M$-controlled subsequential uniformizer.

## Sources

- C. Löding and S. Winter, "Resynchronized Uniformization and Definability Problems for Rational Relations", *Discrete Mathematics & Theoretical Computer Science* 25(2), 2023, doi:[10.46298/dmtcs.7460](https://doi.org/10.46298/dmtcs.7460); read as arXiv:2104.12508v4, whose numbering is used here: Section 2 (uniformization, synchronization languages), Theorems 8 and 9, Lemma 11, Corollaries 12 and 13, Theorem 14 with its proof, and Corollary 15.
