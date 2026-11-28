# Symmetric synthesis for a two-process pipeline is undecidable

No algorithm decides whether an LTL specification can be realized by two identical finite-state processes connected in a pipeline, the first reading the global input and the second reading the first one's output.

**Symmetric architectures.** A process has an *interface* $(\mathsf{AP}^I, \mathsf{AP}^O)$ of local input and output propositions. A *symmetric architecture* over it is a tuple $(S, P, \mathsf{AP}^I_G, E^{\mathit{in}}, E^{\mathit{out}})$ of internal signals $S$, a set $P$ of processes, global input signals $\mathsf{AP}^I_G$, an input edge function $E^{\mathit{in}} \colon P \times \mathsf{AP}^I \to S \cup \mathsf{AP}^I_G$ and an output edge function $E^{\mathit{out}} \colon P \times \mathsf{AP}^O \to S$, every internal signal being written by exactly one local output of one process. Implementations are finite-state machines, which the source takes to be Moore machines. Plugging one finite-state machine with inputs $\mathsf{AP}^I$ and outputs $\mathsf{AP}^O$ into every process gives a machine from $\mathsf{AP}^I_G$ to $S$. Given an interface, an architecture and an LTL specification $\varphi$ over $\mathsf{AP}^I_G \cup S$, the *symmetric synthesis problem* asks whether some finite-state machine implementation makes the resulting system satisfy $\varphi$.

The architecture $S0$ has interface $(\{a\}, \{b\})$, internal signals $S = \{y, z\}$, processes $P = \{0, 1\}$, global input $\mathsf{AP}^I_G = \{x\}$, $E^{\mathit{in}}(0, a) = x$, $E^{\mathit{in}}(1, a) = y$, $E^{\mathit{out}}(0, b) = y$ and $E^{\mathit{out}}(1, b) = z$.

**Theorem (Ehlers and Finkbeiner).** The symmetric synthesis problem for the architecture $S0$ is undecidable.

In contrast, symmetric synthesis is decidable for rotation-symmetric architectures, in which every process reads all global inputs, with complexity doubly exponential in the specification and singly exponential in the number of processes.

## Depends on

- [Formulas of linear temporal logic](../../../Logic/temporal-logic/linear-temporal-logic/formula.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Moore machine](../../regular-languages/automata-and-expressions/sequential-transducers-mealy-and-moore-machines/moore-machine.md)

## Proof depends on

None.

## Expansion

The proof first shows undecidability for a larger symmetric architecture $S2$, by reducing distributed synthesis for the two-process architecture $A0$ of Pnueli and Rosner, which is undecidable: a specification forces the two copies to play the roles of the two different processes of $A0$, using that a process cannot tell whether its local input comes from the environment or from the other process. Undecidability for $S0$ follows by compressing the signals of $S2$ into the single signals $x$, $y$ and $z$ of $S0$.

## Sources

- R. Ehlers and B. Finkbeiner, "Symmetric Synthesis", in *37th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2017)*, Leibniz International Proceedings in Informatics (LIPIcs) 93, 2017, paper 26, doi:10.4230/LIPIcs.FSTTCS.2017.26; read as arXiv:1710.05633v1, <https://arxiv.org/abs/1710.05633v1>: Theorem 14 (the symmetric synthesis problem for $S0$ is undecidable) and Lemma 13 (architecture $S2$), numbered consecutively across environments, the definitions of symmetric architectures and the symmetric synthesis problem with the $S0$ example in Section 3, and Sections 4 and 5 (decidability and complexity for rotation-symmetric architectures), in the numbering of that version.
