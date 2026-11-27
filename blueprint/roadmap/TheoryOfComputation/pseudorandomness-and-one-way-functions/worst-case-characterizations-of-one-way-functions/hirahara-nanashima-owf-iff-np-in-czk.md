# Hirahara–Nanashima: one-way functions exist iff NP ⊆ CZK and NP is worst-case hard (converse of Goldreich–Micali–Wigderson)

For every $\mathsf C\in\{\mathsf{SZKA},\mathsf{CZK},\mathsf{CZKA}\}$ and every constant $\epsilon\in(0,1/2)$ the following are equivalent:

1. There is a one-way function secure against $\mathsf{P/poly}$.
2. $\mathsf{NP}\subseteq\mathsf C$ and $\mathsf{NP}\not\subseteq\mathsf{i.o.P/poly}$.
3. $\mathrm{Gap}_\epsilon\mathrm{MCSP}\in\mathsf C$ and $\mathsf C\not\subseteq\mathsf{i.o.P/poly}$, where $\mathrm{Gap}_\epsilon\mathrm{MCSP}$ distinguishes truth tables of $f:\{0,1\}^n\to\{0,1\}$ of circuit complexity at most $2^{\epsilon n}$ from those of complexity at least $2^{(1-\epsilon)n}$.
4. $(\mathrm{Gap}_\epsilon\mathrm{MCSP},\mathcal U)\in\mathsf{AvgC}$ (an errorless average-case $\mathsf C$ scheme over the uniform distribution) and $\mathsf C\not\subseteq\mathsf{i.o.P/poly}$.

For $\mathsf C=\mathsf{CZK}$ this is the converse of the Goldreich–Micali–Wigderson theorem that one-way functions give computational zero-knowledge proofs for all of $\mathsf{NP}$; for $\mathsf C=\mathsf{SZKA}$ it is the converse of Nguyen–Ong–Vadhan. Statistical zero-knowledge proofs ($\mathsf{SZK}$) are excluded, since $\mathsf{SZK}\subseteq\mathsf{AM}\cap\mathsf{coAM}$ makes $\mathsf{NP}\subseteq\mathsf{SZK}$ unlikely.

## Proof sketch

Items 2, 3, 4 are successively weaker, and item 1 implies item 2 because a one-way function secure against $\mathsf{P/poly}$ gives $\mathsf{NP}\not\subseteq\mathsf{i.o.P/poly}$ and, by Goldreich–Micali–Wigderson (Nguyen–Ong–Vadhan for $\mathsf{SZKA}$), $\mathsf{NP}\subseteq\mathsf C$. The core is item 4 implies item 1, which does not go through Ostrovsky–Wigderson's auxiliary-input one-way function. Let $\Pi\in\mathsf C\setminus\mathsf{i.o.P/poly}$. By the SZK/OWF characterization of Vadhan and Ong–Vadhan, $\Pi$ has the BBR/OWF property: there are polynomial-time auxiliary-input functions $\{f_x\}$ and $\{g_x\}$ and a set $I$ of instances such that $\{f_x\}_{x\in I}$ is one-way against $\mathsf{P/poly}$ almost everywhere on $I$, while on every other instance $\Pi$ is solved by a polynomial-time reduction given any oracle that inverts $g_x$. The distributional problem $(\mathrm{Gap}_\epsilon\mathrm{MCSP},\mathcal U)$ is AIOWF-hard: an errorless average-case algorithm for it yields an inverter for every polynomial-time auxiliary-input function, since it tells random truth tables from those of the auxiliary-input pseudorandom functions built from that function, which have small circuit complexity. Combining the two, $\Pi\notin\mathsf{i.o.P/poly}$ implies that $(\mathrm{Gap}_\epsilon\mathrm{MCSP},\mathcal U)$ is hard on errorless average for $\mathsf{P/poly}$ at all large lengths (a non-black-box worst-case to average-case reduction, which uses the efficiency of the assumed average-case solver). Finally, a generalization of Nanashima's reduction turns this errorless average-case hardness into a one-way function secure against $\mathsf{P/poly}$, using the errorless average-case form of the BBR/OWF property that $(\mathrm{Gap}_\epsilon\mathrm{MCSP},\mathcal U)\in\mathsf{AvgC}$ provides.

## Depends on

- [One-way functions exist](../impagliazzo-s-five-worlds/owfexists.md)
- [Zero-knowledge interactive proofs](../../../ComputerScience/cryptography/signatures-and-protocols/zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)
- [Polynomial time with polynomial advice](../../complexity-classes/time-and-space-complexity-classes/ppoly.md)

## Proof depends on

- [Computational knowledge complexity k(n) of an interactive proof](computational-knowledge-complexity.md)
- [Auxiliary-input one-way functions](auxiliary-input-one-way-functions.md)
- [Ilango–Ren–Santhanam: one-way functions exist iff GapMCSP is average-case hard on some locally samplable distribution](irs-owf-iff-gapmcsp-hard-on-local-distribution.md)

## Sources

- Shuichi Hirahara and Mikito Nanashima, "One-Way Functions and Zero Knowledge", STOC (2024), ECCC TR24-063 (Theorem 2.1; Section 3.2: Definitions 3.1 and 3.3, Lemmas 3.2 and 3.4; Section 5.4).
