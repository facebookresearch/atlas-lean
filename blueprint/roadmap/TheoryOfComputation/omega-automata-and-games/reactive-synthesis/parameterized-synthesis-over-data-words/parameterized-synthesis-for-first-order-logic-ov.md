# Parameterized synthesis for first-order logic over data words is undecidable

When every process may be driven by both the system and the environment and the number of processes is a parameter, no algorithm decides whether the system has a winning strategy for some number of processes, for specifications in two-variable first-order logic with order, successor and the same-process relation, nor for full first-order logic with only the same-process relation.

**Executions.** Processes are controlled by System, by Environment, or by both: $\mathbb{P} = (P_{\mathrm{s}}, P_{\mathrm{e}}, P_{\mathrm{se}})$ is a triple of pairwise disjoint finite sets. A finite action alphabet is split as $A = A_{\mathrm{s}} \uplus A_{\mathrm{e}}$; the *events* are the pairs $(a, p)$ with $a \in A_{\mathrm{s}}$, $p \in P_{\mathrm{s}} \cup P_{\mathrm{se}}$ (System events) or $a \in A_{\mathrm{e}}$, $p \in P_{\mathrm{e}} \cup P_{\mathrm{se}}$ (Environment events). A finite or infinite word of events is a *$\mathbb{P}$-execution*; it is a data word whose data are the processes.

**Logic.** First-order formulas over an execution $w$ have variables ranging over processes and positions of $w$, atomic formulas $\theta(x)$ for the three process types, $a(x)$ (position $x$ carries action $a$), $x = y$, $x \sim y$ (same process, an equivalence relation tying each position to its process), $x < y$ and $+1(x, y)$ on positions, and the Boolean connectives and quantifiers, with the usual [first-order semantics](../../../../Logic/temporal-logic/temporal-specification/first-order-logic-of-order-over-infinite-words.md) extended by the process sort. $\mathrm{FO}[R]$ for $R \subseteq \{\sim, <, +1\}$ uses only the relations in $R$ besides type and action predicates and equality, and $\mathrm{FO}^2[R]$ its two-variable fragment.

**Synthesis.** A System *strategy* maps each finite execution to a System event or to $\varepsilon$ (wait). An execution is compatible with the strategy if each System event in it is the one the strategy prescribes after the preceding prefix, and fair if it is finite only when the strategy then prescribes $\varepsilon$, and, when infinite with infinitely many prescribed System events, contains infinitely many System events. A strategy is winning for a sentence $\varphi$ if every compatible fair execution satisfies $\varphi$. For sets $N_{\mathrm{s}}, N_{\mathrm{e}}, N_{\mathrm{se}} \subseteq \mathbb{N}$, the *parameterized synthesis problem* $\mathrm{Synth}(\mathrm{FO}[R], N_{\mathrm{s}}, N_{\mathrm{e}}, N_{\mathrm{se}})$ asks, given $A = A_{\mathrm{s}} \uplus A_{\mathrm{e}}$ and a sentence $\varphi$, whether there are $\mathbb{P}$ with $(|P_{\mathrm{s}}|, |P_{\mathrm{e}}|, |P_{\mathrm{se}}|) \in N_{\mathrm{s}} \times N_{\mathrm{e}} \times N_{\mathrm{se}}$ and a winning strategy for $\varphi$; with $N_{\mathrm{s}} = \mathbb{N}$ and $N_{\mathrm{e}} = N_{\mathrm{se}} = \{0\}$ it is the satisfiability problem.

**Theorem (Bérard, Bollig, Lehaut and Sznajder).**

1. $\mathrm{Synth}(\mathrm{FO}^2[\sim, <, +1], \{0\}, \{0\}, \mathbb{N})$ is undecidable.
2. $\mathrm{Synth}(\mathrm{FO}[\sim], \{0\}, \{0\}, \mathbb{N})$ is undecidable.

In both cases every process is controlled by both players. By contrast, for $\mathrm{FO}[\sim]$ the problem is decidable when the numbers of Environment and mixed processes are fixed constants, and satisfiability of $\mathrm{FO}^2[\sim, <, +1]$ is decidable, a known result the source cites.

## Depends on

- [First-order logic of order over infinite words](../../../../Logic/temporal-logic/temporal-specification/first-order-logic-of-order-over-infinite-words.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Both proofs reduce the halting problem for two-counter machines. For item 1 the paper adapts the reduction of Figueira and Praveen, given for a fragment of the logic of repeating values, showing that their encoding of two-counter machines can be written with two variables and adapted to the asynchronous setting. For item 2 the paper translates $\mathrm{FO}[\sim]$ formulas into a normal form that only counts processes and the actions of each process up to a threshold, and from there into parameterized vector games; it shows that the game problem with only mixed processes encodes a two-counter machine, and the translation back gives undecidability of synthesis. A complete expansion links the reduction from the logic of repeating values and the undecidability of the parameterized vector game, which have no pages.

## Sources

- B. Bérard, B. Bollig, M. Lehaut and N. Sznajder, "Parameterized synthesis for fragments of first-order logic over data words", in *Foundations of Software Science and Computation Structures (FoSSaCS 2020)*, Lecture Notes in Computer Science, Springer, 2020, pp. 97–118, doi:10.1007/978-3-030-45231-5_6; read in arXiv:1910.14294v1: the definitions of executions, the logic and the synthesis problem in Sections 2 and 3, Theorem on the undecidability for two-variable logic in Section 3 (proved in the appendix), and the theorem on the undecidability of the game and synthesis problems for first-order logic with the same-process relation in Section 5.
