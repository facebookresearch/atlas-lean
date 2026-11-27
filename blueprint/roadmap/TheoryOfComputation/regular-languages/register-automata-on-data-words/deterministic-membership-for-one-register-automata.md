# Deterministic membership of one-register automata is undecidable

No algorithm decides whether the language of a given nondeterministic register automaton with one register is recognized by some deterministic register automaton.

**Theorem.** The DRA membership problem is undecidable for one-register automata: there is no algorithm that, given a nondeterministic [register automaton](register-automata-on-data-words.md) $A$ with one register, decides whether some deterministic register automaton, with any number of registers, recognizes $L(A)$.

When the number $k$ of registers of the deterministic automaton is fixed, the problem becomes decidable for one-register inputs (Theorem 1.2 of the source), although not primitive recursive; for fixed $k$ it is undecidable for two-register inputs and for one-register inputs with guessing (Theorem 1.6 of the source).

## Depends on

- [Register automata on data words](register-automata-on-data-words.md)

## Proof depends on

None.

## Expansion

The proof reduces the finiteness problem for lossy counter machines, which is undecidable (Mayr): does a given machine with $4$ counters, whose counters may spontaneously decrease, reach only finitely many configurations? Runs are encoded as data words over the locations, transitions and counters of the machine, each counter value being written as a block of distinct data values, with reversed matching of values between consecutive blocks. A one-register automaton $A$ accepts exactly the words that are *not* correct encodings. If the reachable set is finite, counter values are bounded by some $k$, the correct encodings form a $k$-register DRA language, and since DRA languages are closed under complement, $L(A)$ is a DRA language. If it is infinite, a DRA with $k$ registers reading a block of more than $k+1$ values must forget one of them, and repeating a forgotten value yields an incorrect encoding that it misclassifies; so $L(A)$ is not a DRA language.

## Sources

- Lorenzo Clemente, Sławomir Lasota and Radosław Piórkowski, "Determinisability of register and timed automata", *Logical Methods in Computer Science* 18(2), 2022, paper 9, doi:[10.46298/lmcs-18(2:9)2022](https://doi.org/10.46298/lmcs-18(2:9)2022); numbering of arXiv:2104.03690v4 ([arXiv](https://arxiv.org/abs/2104.03690v4)): Theorem 1.4 (Section 1.3), its proof in the section on undecidability of DRA membership for one-register automata (encoding of lossy counter machine runs and the lemma relating finiteness to DRA membership); Theorems 1.2 and 1.6.
