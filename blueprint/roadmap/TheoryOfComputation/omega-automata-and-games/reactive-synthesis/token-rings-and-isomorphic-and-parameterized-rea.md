# Token rings and isomorphic and parameterized realizability

In a token ring, identical processes communicate only by passing a token around a ring; isomorphic realizability asks for one
process implementation that satisfies a specification when copied to every position, and parameterized realizability asks for
one that works for rings of every size.

**Architectures and implementations.** An *architecture* $(P, env, V, I, O)$ has a finite set $P$ of processes, containing an
environment $env$ and system processes $1, \dots, k$, a set $V$ of Boolean variables, input sets $I_i \subseteq V$ for the
system processes and output sets $O_i \subseteq V$ for all processes, the $O_i$ partitioning $V$. An *implementation* of
process $i$ is a labeled transition system $(T_i, t_i, \delta_i, o_i)$ with initial state $t_i$, transition function
$\delta_i : T_i \times 2^{I_i} \to T_i$ and labeling $o_i : T_i \to 2^{O_i}$; it is *finite* if $T_i$ is finite. The
composition of implementations moves every process by its own transition function on its inputs, where the outputs of other
processes are read from the current state; a composition *satisfies* an [LTL](../../../Logic/temporal-logic/linear-temporal-logic/formula.md)
formula $\varphi$ if every run, under every sequence of environment outputs, produces a model of $\varphi$. In an
*asynchronous* system the environment also sets scheduling variables $s_i \in I_i$, and process $i$ keeps its state in steps
in which $s_i$ is false.

**Token rings.** In a *token ring* the only communication between system processes is a token: process $i$ holding it may pass
it to process $i + 1$, indices taken modulo $k$, by raising an output $\mathit{send}_i \in O_i \cap I_{i+1}$. Token rings are
asynchronous: in each step one system process moves, except in token-passing steps, where the two processes involved move. A
*parameterized token ring* assigns to each $n$ a token ring with system processes $1, \dots, n$ whose input and output sets are
isomorphic copies of each other, indexed by $i$.

**Realizability.** The *isomorphic realizability problem* for an architecture $A$ and an LTL specification $\varphi$ asks
whether one implementation $\mathcal{T}$ exists such that the composition $(\mathcal{T}, \dots, \mathcal{T})$, the same
implementation at every system process, satisfies $\varphi$. A *parameterized specification* is a prenex indexed LTL sentence,
such as $\forall i.\ \varphi(i)$ or $\forall i \neq j.\ \varphi(i, j)$, and the *parameterized realizability problem* for a
parameterized architecture $\Pi$ asks whether one implementation $\mathcal{T}$ satisfies the specification in $\Pi(n)$ with
$\mathcal{T}$ at every process, for every $n$. *LTL$\setminus$X* is LTL without the next-time operator. The source
distinguishes four forms of parameterized specifications with an LTL$\setminus$X body: (a) $\forall i.\ \varphi(i)$,
(b) $\forall i.\ \varphi(i, i+1)$, (c) $\forall i \neq j.\ \varphi(i, j)$, (d) $\forall i \neq j.\ \varphi(i, i+1, j)$.

By a cutoff theorem of Emerson and Namjoshi, for implementations with fair token passing, parameterized realizability for
these four forms reduces to isomorphic realizability in rings of size at most $2$, $3$, $4$ and $5$, respectively.

## Depends on

- [Formulas of linear temporal logic](../../../Logic/temporal-logic/linear-temporal-logic/formula.md)

## Proof depends on

None.

## Sources

- S. Jacobs and R. Bloem, "Parameterized synthesis", *Logical Methods in Computer Science* 10(1), paper 12, 2014, doi:10.2168/LMCS-10(1:12)2014; numbering of the version arXiv:1401.3588v2: Section 2.1 (architectures, implementations, composition, asynchronous systems, token rings), Section 3.1 (parameterized token rings and specifications, isomorphic and parameterized synthesis), Theorem 3.2 (Emerson and Namjoshi) and Corollary 3.3.
