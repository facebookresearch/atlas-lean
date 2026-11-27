# Equivalence of register automata over polynomials with composition is undecidable

For register automata whose registers hold univariate rational polynomials updated with addition, multiplication and composition, equivalence is undecidable already for deterministic automata on words, and functionality already over a one-letter alphabet.

Let $\mathcal C=(\mathbb Q[x],+,\times,\circ)$ and consider [bottom-up register automata over an algebra](bottom-up-register-automata-over-an-algebra.md) with $\mathcal A=\mathcal C$.

**Theorem.**
1. The equivalence problem for deterministic register automata over $\mathcal C$ is undecidable, even with a monadic input alphabet: no algorithm decides, given two deterministic automata over $\mathcal C$ whose input symbols have rank at most $1$, whether they define the same partial function.
2. The functionality problem for register automata over $\mathcal C$ is undecidable, even with a monadic input alphabet having one unary letter $a$ and one constant $\bot$, i.e. inputs $a^k\bot$.

In particular, functionality and equivalence of functional automata over $\mathcal C$ are undecidable. Without composition, both are decidable over $(\mathbb Q[X],+,\times)$; the source reduces equivalence of macro tree transducers to equivalence over $\mathcal C$, so the decidability proof by the Hilbert method does not extend to macro tree transducers along this route.

## Depends on

- [Bottom-up register automata over an algebra](bottom-up-register-automata-over-an-algebra.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from control-state reachability in a two-counter machine with states $1,\dots,n$, started in $(1,0,0)$, target state $n$. The automaton $M'$ has a single state and reads words over the transitions of the machine (rank $1$) ended by a constant $\bot$. Six registers hold: the current state $r_q$ and counters $r_{c_1},r_{c_2}$ as constant polynomials; the step count $r_+=m$; the polynomial $r_{zt}=\prod_{j=1}^{m}(x-j)$, which is nonzero at $0$ and vanishes at $1,\dots,m$ (counters never exceed $m$ after $m$ steps); and a witness $r_w$. Reading a transition $(i,b_1,b_2)\to(j,d_1,d_2)$ updates the configuration, sets $r_+\leftarrow r_++1$ and $r_{zt}\leftarrow r_{zt}\times(x-r_+-1)$, and multiplies $r_w$ by $P_i\circ r_q$, where $P_i=\prod_{j\neq i}(x-j)$ vanishes exactly at the states other than $i$, and, for each counter, by $r_{c_k}$ if the transition assumes it nonzero or by $r_{zt}\circ r_{c_k}$ if it assumes it zero. By induction, $r_w=0$ exactly when the word is not a valid run. The output is $(P_n\circ r_q)\times r_w$, so $[\![M']\!]$ is the constant $0$ function iff state $n$ is unreachable. Comparing $M'$ with an automaton that outputs $0$ gives undecidability of equivalence of deterministic monadic automata; running both nondeterministically (or, over the alphabet $\{a,\bot\}$, guessing at each letter which transition to simulate) gives undecidability of functionality.

## Sources

- Adrien Boiret, Radosław Piórkowski and Janusz Schmude, "Reducing Transducer Equivalence to Register Automata Problems Solved by \"Hilbert Method\"", in *FSTTCS 2018*, LIPIcs 122, 2018, pp. 48:1–48:16, doi:[10.4230/LIPIcs.FSTTCS.2018.48](https://doi.org/10.4230/LIPIcs.FSTTCS.2018.48); numbering of arXiv:1806.04361v2 ([arXiv](https://arxiv.org/abs/1806.04361v2)): Section 4: the first theorem of the section (functionality and equivalence of functional automata over $(\mathbb Q[x],+,\times,\circ)$ are undecidable), the definition of two-counter machines and their reachability problem, and the strengthened theorem at the end of the section (deterministic monadic equivalence and one-letter functionality); the decidable case over $(\mathbb Q[X],+,\times)$ is the theorem at the end of Section 2.
