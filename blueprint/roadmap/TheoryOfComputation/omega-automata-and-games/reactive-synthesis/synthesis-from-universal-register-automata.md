# Register transducer synthesis from universal register automata is undecidable

No algorithm decides whether a specification given by a universal register automaton over data words is realized by some register transducer with any number of registers.

**Theorem.** $\mathrm{Real}(\mathrm{URA},\mathrm{RT})$ is undecidable: there is no algorithm that, given a [specification](register-transducer-synthesis-from-data-word.md) defined by a universal parity register automaton, decides whether some register transducer, with no bound on its number of registers, realizes it.

In contrast, bounded synthesis from URA specifications, with a fixed bound $k$ on the registers of the transducer, is decidable (Khalimov, Maderbacher and Bloem; the source gives a generic proof), so the undecidability is specific to the unbounded problem, which answers a question they left open.

## Depends on

- [Register transducer synthesis from data-word specifications](register-transducer-synthesis-from-data-word.md)

## Proof depends on

None.

## Expansion

The reduction is from emptiness of universal register automata over finite data words, which is undecidable by duality with universality of nondeterministic ones. The relation $S_1=\{(u\#v,u\#w): \text{every datum of } u \text{ occurs infinitely often in } w\}$ is recognized by a one-register URA; its restriction to words $u$ with at most $k$ distinct data is realized with $k$ registers (output them in round-robin), but $S_1$ itself is not realizable, since at $\#$ a transducer would need all data of $u$ in its registers. Given $A$, the specification $S=S_1\cup S_2\cup T$ adds $S_2=\{(u\#v,u\#w\#(a,d_0)^\omega): w\in L(A)\}$ and the identity-like part $T$ for inputs without $\#$; $S$ is URA-recognizable with total domain. If some $w\in L(A)$ uses $k$ data, a transducer with $k+2$ registers realizes $S$: after $\#$ it follows $S_1$ when $u$ has at most $k$ data and otherwise outputs a renaming of $w$ into data of $u$, accepted by $A$ because register automata are invariant under renaming data. If $L(A)=\emptyset$, a realizer of $S$ would realize $S_1$, which is impossible.

## Sources

- Léo Exibard, Emmanuel Filiot and Pierre-Alain Reynier, "Synthesis of Data Word Transducers", *Logical Methods in Computer Science* 17(1), 2021, paper 22, doi:[10.23638/LMCS-17(1:22)2021](https://doi.org/10.23638/LMCS-17(1:22)2021); numbering of arXiv:1905.03538v5 ([arXiv](https://arxiv.org/abs/1905.03538v5)): Theorem 4.3 and its proof; Section 5.2 (bounded synthesis for URA specifications).
