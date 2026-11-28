# Register transducer synthesis from data-word specifications

In synthesis over data words, a specification is a register automaton reading interleaved input and output letters carrying data from an infinite domain, and the realizability problem asks for a register transducer that answers every input with outputs satisfying it.

Let $\mathcal D$ be a countably infinite set of data with a distinguished value $d_0$, and $\Sigma$ a finite alphabet. A *data word* is an infinite sequence in $(\Sigma\times\mathcal D)^\omega$. For a finite set $R$ of registers, a *test* is a Boolean combination of atoms $r^=$ and $r^{\ne}$ ($r\in R$), true for a register valuation $\tau:R\to\mathcal D$ and a datum $d$ when $\tau(r)=d$, respectively $\tau(r)\neq d$.

**Register automata.** A *register automaton* $(\Sigma,\mathcal D,Q,q_0,\delta,R,c)$ has finite states $Q$, initial state $q_0$, registers $R$ (all initially $d_0$), a priority function $c:Q\to\{1,\dots,d\}$ and transitions $(q,\sigma,\phi,A,q')$: on $(\sigma,d)$, if $d$ satisfies the test $\phi$, it stores $d$ in the registers of $A\subseteq R$ and moves to $q'$. A run is accepting if the largest priority seen infinitely often is even. Read *nondeterministically* (NRA) it accepts a data word when some run is accepting; read *universally* (URA) when all runs are; it is deterministic (DRA) when tests of transitions with the same state and letter are mutually exclusive.

**Specifications and implementations.** For finite alphabets $\Sigma_i,\Sigma_o$, a *specification* is a set $S$ of relational data words in $((\Sigma_i\times\mathcal D)(\Sigma_o\times\mathcal D))^\omega$, here given by a register automaton whose states alternate between reading an input and an output letter. A *register transducer* $(\Sigma_i,\Sigma_o,Q,q_0,\delta,R)$ has a complete transition function $\delta:Q\times\Sigma_i\times\mathrm{Tests}_R\to 2^R\times\Sigma_o\times R\times Q$: reading $(\sigma,d)$ it tests $d$ against its registers, stores $d$ in some registers, and outputs a letter together with the content of one register. It defines a function from input to output data words and the set of interleavings of inputs with their outputs. A transducer *realizes* $S$ when this set is included in $S$. $\mathrm{RT}[k]$ denotes transducers with at most $k$ registers and $\mathrm{RT}=\bigcup_k\mathrm{RT}[k]$. For a class $\mathcal S$ of specification automata and a class $\mathcal I$ of implementations, $\mathrm{Real}(\mathcal S,\mathcal I)$ asks whether a given specification in $\mathcal S$ is realized by some implementation in $\mathcal I$.

## Depends on

- [Even max-parity condition](../parity-condition-on-infinite-sequences/parity-even.md)

## Proof depends on

None.

## Expansion

A server granting the requests of unboundedly many clients, each request to be eventually granted with the client's identifier, is specified by a one-register URA and realized by a transducer that copies each request's identifier into its grant. For data-free specifications this is Church's synthesis problem, as in [realizability of specifications over infinite words](realizability-of-specifications-over-infinite.md).

## Sources

- Léo Exibard, Emmanuel Filiot and Pierre-Alain Reynier, "Synthesis of Data Word Transducers", *Logical Methods in Computer Science* 17(1), 2021, paper 22, doi:[10.23638/LMCS-17(1:22)2021](https://doi.org/10.23638/LMCS-17(1:22)2021); numbering of arXiv:1905.03538v5 ([arXiv](https://arxiv.org/abs/1905.03538v5)): Section 1 (data words, register automata, runs and the NRA, URA and DRA semantics) and Section 2 (specifications, implementations, the realizability problem, specification register automata and register transducers).
