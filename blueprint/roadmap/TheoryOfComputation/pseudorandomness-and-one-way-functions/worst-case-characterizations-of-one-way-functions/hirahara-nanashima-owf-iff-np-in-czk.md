# Hirahara–Nanashima: one-way functions exist iff NP ⊆ CZK and NP is worst-case hard (converse of Goldreich–Micali–Wigderson)

For every $\mathsf C\in\{\mathsf{SZKA},\mathsf{CZK},\mathsf{CZKA}\}$ and every constant $\epsilon\in(0,1/2)$ the following are equivalent:

1. There is a one-way function secure against $\mathsf{P/poly}$.
2. $\mathsf{NP}\subseteq\mathsf C$ and $\mathsf{NP}\not\subseteq\mathsf{i.o.P/poly}$.
3. $\mathrm{Gap}_\epsilon\mathrm{MCSP}\in\mathsf C$ and $\mathsf C\not\subseteq\mathsf{i.o.P/poly}$, where $\mathrm{Gap}_\epsilon\mathrm{MCSP}$ distinguishes truth tables of $f:\{0,1\}^n\to\{0,1\}$ of circuit complexity at most $2^{\epsilon n}$ from those of complexity at least $2^{(1-\epsilon)n}$.
4. $(\mathrm{Gap}_\epsilon\mathrm{MCSP},\mathcal U)\in\mathsf{AvgC}$ (an errorless average-case $\mathsf C$ scheme over the uniform distribution) and $\mathsf C\not\subseteq\mathsf{i.o.P/poly}$.

For $\mathsf C=\mathsf{CZK}$ this is the converse of the Goldreich–Micali–Wigderson theorem that one-way functions give computational zero-knowledge proofs for all of $\mathsf{NP}$; for $\mathsf C=\mathsf{SZKA}$ it is the converse of Nguyen–Ong–Vadhan. Statistical zero-knowledge proofs ($\mathsf{SZK}$) are excluded, since $\mathsf{SZK}\subseteq\mathsf{AM}\cap\mathsf{coAM}$ makes $\mathsf{NP}\subseteq\mathsf{SZK}$ unlikely.

## Proof sketch

Items 2, 3, 4 are successively weaker. The core is item 4 implies item 1: by Ostrovsky–Wigderson, $\mathsf C\not\subseteq\mathsf{i.o.P/poly}$ gives an auxiliary-input one-way function, and a generalization of Nanashima's reduction shows that a zero-knowledge scheme for $\mathrm{Gap}_\epsilon\mathrm{MCSP}$ on average, run against the simulator of the auxiliary-input one-way function, either inverts it or produces a standard one-way function. Zero knowledge is used to argue that the verifier's view, which can be simulated, reveals nothing that distinguishes YES instances drawn from the function's outputs from random truth tables.

## Depends on

- [One-way functions exist](../impagliazzo-s-five-worlds/owfexists.md)
- [Zero-knowledge interactive proofs](../../../ComputerScience/cryptography/signatures-and-protocols/zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)
- [Polynomial time with polynomial advice](../../complexity-classes/time-and-space-complexity-classes/ppoly.md)

## Proof depends on

- [Computational knowledge complexity k(n) of an interactive proof](computational-knowledge-complexity.md)
- [Auxiliary-input one-way functions](auxiliary-input-one-way-functions.md)
- [Ilango–Ren–Santhanam: one-way functions exist iff GapMCSP is average-case hard on some locally samplable distribution](irs-owf-iff-gapmcsp-hard-on-local-distribution.md)

## Sources

- Shuichi Hirahara and Mikito Nanashima, "One-Way Functions and Zero Knowledge", STOC (2024), ECCC TR24-063.
