# Regularity of probabilistic weak automata is undecidable

No algorithm decides whether the language of a probabilistic weak automaton over infinite words is $\omega$-regular, under positive, almost-sure or threshold semantics.

**Probabilistic Büchi automata.** A *probabilistic Büchi automaton* is a tuple $\mathcal{A} = (Q, \Sigma, \delta, \mu_0, F)$ with a finite set $Q$ of states, a finite alphabet $\Sigma$, a transition function $\delta \colon Q \times \Sigma \times Q \to [0,1]$ with $\sum_{q} \delta(p, a, q) = 1$ for all $p \in Q$ and $a \in \Sigma$, an initial distribution $\mu_0$ on $Q$, and a set $F \subseteq Q$ of final states. On an infinite word $w \in \Sigma^\omega$ the transition probabilities induce a probability measure on the runs of $\mathcal{A}$ on $w$; a run is *accepting* if it visits $F$ infinitely often. For a fixed $\lambda$ with $0 < \lambda < 1$ the languages

$$
L^{>0}(\mathcal{A}),\qquad L^{=1}(\mathcal{A}),\qquad L^{>\lambda}(\mathcal{A})
$$

consist of the words whose set of accepting runs has probability $> 0$, $= 1$ and $> \lambda$, respectively (*positive*, *almost-sure* and *threshold* semantics). As inputs, automata have rational transition probabilities and initial distribution.

**Weakness.** The *underlying graph* of $\mathcal{A}$ has an edge $p \to q$ labeled $a$ whenever $\delta(p, a, q) > 0$. The automaton is *weak* if $F$ is a union of strongly connected components of this graph; then every run eventually stays in one component, and it is accepting exactly when that component lies in $F$. A weak probabilistic Büchi automaton is a *probabilistic weak automaton*.

**Theorem (Löding and Pirogov).** For each of the positive, almost-sure and threshold semantics, there is no algorithm that decides, given a probabilistic weak automaton $\mathcal{A}$, whether its language is $\omega$-regular. Consequently, regularity is undecidable for probabilistic Büchi automata under each semantics.

The proof also shows that, for a suitable fixed $\omega$-regular language $L$, it is undecidable whether a given probabilistic weak automaton accepts exactly $L$. Under almost-sure semantics emptiness and universality of probabilistic Büchi automata are decidable, as the source recalls, so undecidability of regularity does not follow from undecidability of emptiness there.

## Depends on

- [Büchi acceptance condition](../emptiness-of-b-chi-automata/mem-language-iff.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The value-1 problem for probabilistic automata is undecidable](../../regular-languages/automata-and-expressions/weighted-automata-and-rational-series/value-1-problem-for-probabilistic-automata.md)
- [Büchi automata are closed under complementation](../boolean-closure-of-b-chi-automata/exists-buchi-compl.md)
- [Nonempty Büchi languages contain ultimately periodic words](../emptiness-of-b-chi-automata/exists-lasso-word-of-nonempty.md)

## Expansion

Since $\omega$-regular languages are closed under complement, $L^{>0}(\mathcal{A})$ is the complement of an almost-sure language, and every positive language is also a threshold language, it suffices to treat almost-sure semantics. The reduction starts from the value-1 problem for probabilistic automata on finite words, restricted to automata that accept no finite word with probability $1$ (that restriction is decidable by a subset construction). Given such an automaton $\mathcal{A}$ over $\Sigma$, one builds a probabilistic weak automaton $\mathcal{B}$ over $\Sigma \cup \{\#\}$ from a copy of $\mathcal{A}$: on $\#$, accepting states of $\mathcal{A}$ restart the copy, while non-accepting states lead into a new part that ensures that infinitely many $\#$ are seen and contains the only accepting state of $\mathcal{B}$. Then $L^{=1}(\mathcal{B}) = (\Sigma^* \#)^\omega \setminus R$, where $R = \varnothing$ if $\mathcal{A}$ does not have value $1$, and otherwise $R$ is nonempty but contains no ultimately periodic word. Since a nonempty $\omega$-regular language contains an ultimately periodic word, $L^{=1}(\mathcal{B})$ is $\omega$-regular if and only if $\mathcal{A}$ does not have value $1$.

## Sources

- C. Löding and A. Pirogov, "Ambiguity, Weakness, and Regularity in Probabilistic Büchi Automata", in *Foundations of Software Science and Computation Structures (FoSSaCS 2020)*, Lecture Notes in Computer Science, Springer, 2020, pp. 522–541, doi:10.1007/978-3-030-45231-5_27; read as arXiv:2004.13692v1, <https://arxiv.org/abs/2004.13692v1>: Theorem 7 (regularity of probabilistic weak automata under positive, almost-sure and threshold semantics) with the proof sketch after it and the proof in the appendix section on weak automata, the definitions of probabilistic automata, weakness and the three semantics in Section 2, and the introduction (fixed regular language; decidability of emptiness and universality under almost-sure semantics), in the numbering of that version.
