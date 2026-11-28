# Determinization notions for one-counter nets

A one-counter net is a finite automaton with a natural-number counter that transitions change by integer amounts without ever testing it
for zero; since its language depends on the initial counter value, asking whether it has an equivalent deterministic net splits into four
different questions.

**One-counter nets.** A *one-counter net* (OCN) $\mathcal{A} = (\Sigma, Q, s_0, \delta, F)$ has a finite alphabet $\Sigma$, a finite set $Q$ of states, an initial state $s_0$,
a finite transition relation $\delta \subseteq Q \times \Sigma \times \mathbb{Z} \times Q$ and accepting states $F \subseteq Q$. Configurations are pairs $(s, v) \in Q \times \mathbb{N}$, and
$(s, v) \xrightarrow{\sigma} (s', v + d)$ for a transition $(s, \sigma, d, s')$ provided $v + d \ge 0$. A word is accepted from initial counter $c$ if some run on it
from $(s_0, c)$ ends in an accepting state; $\mathcal{L}(\mathcal{A}, c)$ is the set of such words, and $\mathcal{L}(\mathcal{A}, c) \subseteq \mathcal{L}(\mathcal{A}, c')$ when $c \le c'$. The net is
*deterministic* (a DOCN) if every state and letter have at most one outgoing transition. As an input, an OCN is given by its finite tables, with each effect $d$ written as an integer.

**Determinization notions.** For an OCN $\mathcal{A}$:

- $\mathcal{A}$ is *0-determinizable* if some DOCN $\mathcal{D}$ has $\mathcal{L}(\mathcal{A}, 0) = \mathcal{L}(\mathcal{D}, 0)$;
- $\mathcal{A}$ is *$\exists$-determinizable* if for some $c \in \mathbb{N}$ some DOCN $\mathcal{D}$ has $\mathcal{L}(\mathcal{A}, c) = \mathcal{L}(\mathcal{D}, 0)$;
- $\mathcal{A}$ is *$\forall$-determinizable* if for every $c \in \mathbb{N}$ some DOCN $\mathcal{D}$ has $\mathcal{L}(\mathcal{A}, c) = \mathcal{L}(\mathcal{D}, 0)$;
- $\mathcal{A}$ is *uniformly determinizable* if some DOCN $\mathcal{D}$ has $\mathcal{L}(\mathcal{A}, c) = \mathcal{L}(\mathcal{D}, c)$ for every $c \in \mathbb{N}$.

Every uniformly determinizable net is $\forall$-determinizable, every $\forall$-determinizable net is $0$-determinizable, and every $0$-determinizable net is
$\exists$-determinizable; none of these inclusions is an equality.

## Depends on

- [One-counter automata and one-counter nets](../../extended-finite-automata/regular-separability-of-one-counter-automata/one-counter-automata-and-one-counter-nets.md)

## Proof depends on

None.

## Sources

- S. Almagor and A. Yeshurun, "Determinization of one-counter nets", in *33rd International Conference on Concurrency Theory (CONCUR 2022)*, LIPIcs 243, paper 18, 2022, doi:10.4230/LIPIcs.CONCUR.2022.18; read in arXiv:2112.13716v1: Section 1 (the four determinization notions), Section 2 (one-counter nets, runs and languages) and Section 3 (Observation 1 on implications and Lemma 2 with the separating examples), with the numbering of that version.
