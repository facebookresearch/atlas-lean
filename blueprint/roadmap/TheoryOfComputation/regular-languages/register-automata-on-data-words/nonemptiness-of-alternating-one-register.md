# Nonemptiness of alternating one-register automata on data ω-words is undecidable

For one-way alternating automata with one register reading infinite data words, nonemptiness is undecidable under weak, Büchi or co-Büchi acceptance, while with safety acceptance it is EXPSPACE-complete; for the corresponding temporal logic, past operators or a second register restore undecidability even in the safety fragment.

A *data $\omega$-word* over a finite alphabet $\Sigma$ is an $\omega$-word over $\Sigma$ together with an equivalence relation $\sim$ on its positions $\mathbb N$, whose classes are the *data*; this abstracts infinite words over $\Sigma\times\mathbb A$ for an infinite set $\mathbb A$ of data values compared only for equality (see [register automata on data words](register-automata-on-data-words.md)). A *one-way alternating automaton with one register* (1ARA$_1$) has finitely many states, an initial state and a transition function $\delta(q,\sigma,\uparrow\text{ or }\nuparrow)$ into positive Boolean formulas over atoms $q'$ and ${\downarrow}q'$. A configuration at position $i$ is a state with a register value (a class of $\sim$); depending on the letter at $i$ and on whether the register holds the class of $i$ ($\uparrow$) or not ($\nuparrow$), each configuration chooses sets of successor states satisfying the formula, those under ${\downarrow}$ storing the class of $i$ in the register and the others keeping the old value. Runs are sequences of sets of configurations, and acceptance is given by a weak, Büchi, co-Büchi or safety condition (safety: every infinite run accepts).

**Theorem.**
1. Nonemptiness of 1ARA$_1$ on data $\omega$-words with weak acceptance, and hence with Büchi or co-Büchi acceptance, is undecidable, more precisely $\Pi^0_1$-hard (Demri and Lazić).
2. Satisfiability on data $\omega$-words of future-time LTL with one register (freeze quantifier) is $\Pi^0_1$-hard, and so is its safety fragment once past temporal operators or a second register are added (Demri and Lazić).
3. By contrast, nonemptiness of *safety* 1ARA$_1$, and satisfiability of the safety fragment of future-time LTL with one register, are EXPSPACE-complete, and their inclusion and refinement problems are decidable but not primitive recursive (Lazić).

Over finite data words, nonemptiness of 1ARA$_1$ is decidable but not primitive recursive (Demri and Lazić).

## Depends on

- [Register automata on data words](register-automata-on-data-words.md)
- [Alternating Büchi automata](../../omega-automata-and-games/alternating-automata/alternating-buchi-automata.md)
- [The arithmetical class $\Pi_n$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Formulas of linear temporal logic](../../../Logic/temporal-logic/linear-temporal-logic/formula.md)

## Proof depends on

None.

## Expansion

Items 1 and 2 are Theorem 5.2 of Demri and Lazić and a consequence of the proof of their Theorem 5.4; the source read recalls them without proof. Item 3 is the source's contribution: safety 1ARA$_1$ are translated in polynomial space into safety incrementing counter automata with zero tests, whose nonemptiness is decided in exponential space, future-time safety LTL with one register translates into safety 1ARA$_1$ in logarithmic space, and a matching EXPSPACE lower bound is shown for the logic; inclusion is decided through a well-quasi-ordering of counter configurations.

## Sources

- Ranko Lazić, "Safety alternating automata on data words", *ACM Transactions on Computational Logic* 12(2), 2011, article 10, pp. 1–24, doi:[10.1145/1877714.1877716](https://doi.org/10.1145/1877714.1877716); read in arXiv:0802.4237v3 ([arXiv](https://arxiv.org/abs/0802.4237v3)): the abstract, the introduction (state of the art and contribution) and Section 2 (data words, register automata).
- The undecidability results are due to Stéphane Demri and Ranko Lazić, "LTL with the freeze quantifier and register automata", *ACM Transactions on Computational Logic* 10(3), 2009, article 16, pp. 1–30, doi:[10.1145/1507244.1507246](https://doi.org/10.1145/1507244.1507246), Theorem 5.2 and the proof of Theorem 5.4, as recalled in the source above (not read).
