# Register automata on data words

A register automaton reads finite words of pairs (letter, data value) from an infinite set of data values, storing finitely many input data values in registers and comparing the current value with them for equality; it is deterministic when its transitions never overlap.

Let $\mathbb A$ be a countably infinite set of *data values* (atoms) compared only for equality, and $\Sigma$ a finite alphabet. A *data word* is a finite sequence $(\sigma_0,a_0)\cdots(\sigma_n,a_n)\in(\Sigma\times\mathbb A)^*$. Fix a finite set $X=\{x_1,\dots,x_k\}$ of *registers*; a register valuation is $\mu:X\to\mathbb A\cup\{\bot\}$, $\bot$ meaning undefined. A *constraint* is a Boolean combination of equalities $x=y$ and $x=\bot$ between registers and a variable $y$ for the input value.

A (nondeterministic) *register automaton* (NRA) with $k$ registers is a tuple $(X,\Sigma,L,L_I,L_F,\Delta)$ with a finite set $L$ of locations, initial and final locations $L_I,L_F\subseteq L$, and transition rules $(p,\sigma,\varphi,Y,q)$: from $(p,\mu)$, reading $(\sigma,a)$, the automaton may move to $(q,\mu[Y\mapsto a])$ if $\varphi$ is true for $y=a$, which stores the input value in the registers of $Y$. (Rules without input, $\varepsilon$-rules, can be eliminated for one register.) Runs start with all registers undefined in an initial location, and a data word is accepted if some run over it ends in a final location; $L(A)$ is the set of accepted data words. Registers only ever hold values read from the input (no *guessing*). The automaton is *deterministic* (a DRA) if it has one initial location and any two rules from the same location with the same letter and jointly satisfiable constraints have the same register set and target, so that each data word has at most one run.

The *DRA membership problem* asks, given an NRA $A$, whether $L(A)=L(B)$ for some DRA $B$ (with any number of registers); the *$k$-DRA membership problem* bounds the registers of $B$ by a fixed $k$.

## Depends on

None.

## Proof depends on

None.

## Expansion

NRA languages are not closed under complement and NRA universality is undecidable, already with two registers, while DRA languages are closed under complement; a data language is a DRA language iff it and its complement are NRA languages. With one register, inclusion of an NRA in a one-register NRA is decidable, though not primitive recursive.

## Sources

- Lorenzo Clemente, Sławomir Lasota and Radosław Piórkowski, "Determinisability of register and timed automata", *Logical Methods in Computer Science* 18(2), 2022, paper 9, doi:[10.46298/lmcs-18(2:9)2022](https://doi.org/10.46298/lmcs-18(2:9)2022); numbering of arXiv:2104.03690v4 ([arXiv](https://arxiv.org/abs/2104.03690v4)): Section 1.1 (register automata and known results), Section 1.2 (deterministic membership problems), and the appendix section on register automata over equality atoms (constraints, NRAs, runs, DRAs).
