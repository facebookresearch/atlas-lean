# Emptiness of unary realtime alternating one-counter automata is undecidable

No algorithm decides, given a realtime alternating one-counter automaton over a one-letter input alphabet, whether it accepts some input.

**Theorem.** The emptiness problem for unary [realtime alternating one-counter automata](realtime-alternating-one-counter-automata.md) is undecidable: there is no algorithm that, given an A1CA $A$ with input alphabet $\{u\}$, decides whether $A$ accepts some word $u^m$, $m\ge 0$.

For comparison, the source recalls that for one-way pushdown automata emptiness is decidable while universality is undecidable, so emptiness is undecidable for pushdown automata with only universal branching; the theorem shows that alternation with a single counter already gives undecidability over a one-letter alphabet.

## Depends on

- [Realtime alternating one-counter automata](realtime-alternating-one-counter-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Given a deterministic Turing machine $M$, normalized to have a semi-infinite tape with a fixed left-end symbol in cell $0$ and to halt, in a unique state $q_f$, exactly when its head first returns to cell $0$, the proof builds an A1CA $A$ that accepts $u^{2n}$ exactly when $M$, started on the empty tape, halts after exactly $n$ steps; so $A$ accepts some input if and only if $M$ halts on the empty tape.

The input $u^{2n}$ serves as a clock and the counter as a pointer $C$ to a tape cell. The simulation runs backwards (as in Theorem 3.4 of Chandra, Kozen and Stockmeyer, which the source cites): since $M$ is deterministic, the content of cell $C$ at step $t$ (a tape symbol, or a state-symbol pair where the head is) is a fixed function $\mathrm{Next}_M$ of the contents of cells $C-1$, $C$, $C+1$ at step $t-1$. Starting from the halting configuration (state $q_f$ on cell $0$, counter $0$), $A$ keeps a claimed content $s$ in its finite memory; on one input symbol it guesses existentially a triple $(s_{-1},s_0,s_1)$ with $\mathrm{Next}_M(s_{-1},s_0,s_1)=s$, and on the next symbol it branches universally to check $s_d$ at cell $C+d$, $d\in\{-1,0,1\}$, one step earlier. When the input is exhausted, a branch accepts only if its claim agrees with the initial configuration of $M$.

## Sources

- H. Gökalp Demirci, Mika Hirvensalo, Klaus Reinhardt, A. C. Cem Say and Abuzer Yakaryılmaz, "Alternating, private alternating, and quantum alternating realtime automata", *Logical Methods in Computer Science* 15(3), 2019, paper 22, doi:[10.23638/LMCS-15(3:22)2019](https://doi.org/10.23638/LMCS-15(3:22)2019); numbering of arXiv:1407.0334v5 ([arXiv](https://arxiv.org/abs/1407.0334v5)): Theorem 2.1 and its proof.
