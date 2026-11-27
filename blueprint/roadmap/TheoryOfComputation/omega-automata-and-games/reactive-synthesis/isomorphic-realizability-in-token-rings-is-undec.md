# Isomorphic realizability in token rings is undecidable

No algorithm decides whether an LTL specification without the next-time operator is realized in a token ring by copies of a
single process implementation, already for rings with two processes.

**Theorem.** For every fixed number $k \ge 2$ of system processes, the
[isomorphic realizability problem](token-rings-and-isomorphic-and-parameterized-rea.md) is undecidable for token rings with $k$
processes and specifications in LTL$\setminus$X: given such a token ring and a specification $\varphi$, it is undecidable
whether a single implementation $\mathcal{T}$ exists such that the ring with $\mathcal{T}$ at every process satisfies
$\varphi$.

When the simulated machine halts, the specification of the reduction is realized by a finite implementation, and otherwise it
is not realizable at all, so the problem remains undecidable when the implementation is required to be finite. Distributed realizability was known to be undecidable for
two synchronous processes with incomparable information (Pnueli and Rosner); here the processes are identical, asynchronous,
and can communicate only through the token.

## Depends on

- [Token rings and isomorphic and parameterized realizability](token-rings-and-isomorphic-and-parameterized-rea.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The proof adapts Pnueli and Rosner's reduction from the halting problem of deterministic Turing machines. Two processes
receive start signals from the environment and must each output the successive configurations of the machine, separated by
blanks; because neither sees the other, the specification that relates their outputs (equal configurations after equally many
start signals, successor configurations when one process is one signal ahead) forces both to simulate the machine, and adding
that the halting state must eventually be output makes the specification realizable if and only if the machine halts. For token
rings, one synchronous step becomes one full cycle of the token, with fair scheduling and fair token passing, a designated
initial token holder, and the requirement that each process changes its outputs only when it receives the token; the token
carries no information beyond synchronization. Each next-time operator $\mathsf{X}\,\psi$ is replaced by an LTL$\setminus$X
formula saying that $\psi$ holds at the next state in which process $1$ receives the token. Since any correct implementation of
one process also works for the other, isomorphic realizability is equivalent to realizability, and additional processes get the
specification of process $2$.

## Sources

- S. Jacobs and R. Bloem, "Parameterized synthesis", *Logical Methods in Computer Science* 10(1), paper 12, 2014, doi:10.2168/LMCS-10(1:12)2014; Theorem 3.4 of the version arXiv:1401.3588v2 with its proof.
