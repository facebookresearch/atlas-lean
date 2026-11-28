# Qualitative zero-reachability in probabilistic multi-counter automata is undecidable

For probabilistic multi-counter automata, deciding whether a run almost surely reaches a configuration in which a prescribed set of counters is simultaneously zero is undecidable already in dimension $2$ when the stopping sets require two counters to be zero together, and in dimension $3$ when two counters are never tested.

**Probabilistic multi-counter automata.** A $d$-dimensional *probabilistic multi-counter automaton* is a triple $\mathcal{A} = (Q, \gamma, W)$ with a finite set $Q$ of states, a set $\gamma \subseteq Q \times \{-1, 0, 1\}^d \times 2^{\{1, \dots, d\}} \times Q$ of rules such that every state $p$ and every set $c$ of counters has at least one rule $(p, \alpha, c, q)$, and a weight assignment $W \colon \gamma \to \mathbb{N}^+$. A configuration $p\vec{v}$ has a state $p$ and counter values $\vec{v} \in \mathbb{N}^d$; let $Z(p\vec{v})$ be the set of counters that are zero. A rule $(p, \alpha, c, q)$ is enabled in $p\vec{v}$ if $Z(p\vec{v}) = c$ and every counter decremented by $\alpha$ is positive. The automaton defines a Markov chain on configurations: from $p\vec{v}$ each enabled rule fires with probability its weight divided by the total weight of the enabled rules, leading to $q(\vec{v} + \alpha)$; a configuration with no enabled rule loops with probability $1$.

**Stopping criteria.** A *stopping criterion* is a nonempty set $\mathcal{Z} \subseteq 2^{\{1, \dots, d\}}$ of pairwise incomparable nonempty sets of counters. A run is *stopped* if it visits a configuration $p\vec{v}$ with $\varrho \subseteq Z(p\vec{v})$ for some $\varrho \in \mathcal{Z}$. The *qualitative $\mathcal{Z}$-reachability problem* asks, given $\mathcal{A}$ and a state $p$, whether the run from $p\vec{1}$, with every counter equal to $1$, is stopped with probability $1$.

**Observation (Brázdil, Kiefer, Kučera, Novotný and Katoen).** Let $\mathcal{Z}$ be a stopping criterion such that

1. some $\varrho \in \mathcal{Z}$ has more than one element, or
2. there are distinct counters $i, j$ with $\{i, j\} \cap \varrho = \varnothing$ for every $\varrho \in \mathcal{Z}$.

Then the qualitative $\mathcal{Z}$-reachability problem is undecidable, even for instances in which the probability of being stopped is either $0$ or $1$. Hence that probability cannot be computed up to an absolute error smaller than $0.5$ (Observation 1 of the source).

The two stopping criteria not covered, $\{\{1\}, \dots, \{d\}\}$ (stop when some counter is zero) and that set with one singleton removed, are analyzed separately in the same paper.

## Depends on

- [Probabilistic counter machines and decisiveness](../decisiveness-of-probabilistic-counter-systems/probabilistic-counter-machines-and-decisiveness.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem for two-counter Minsky machines started with both counters at $1$. For condition 2, a $3$-dimensional automaton simulates the machine on counters $1$ and $2$ and decreases counter $3$ to zero only when the halting instruction is reached, with $\mathcal{Z} = \{\{3\}\}$. For condition 1, a $2$-dimensional automaton with $\mathcal{Z} = \{\{1, 2\}\}$ first increases both counters and then decreases or increases counter $i$ before or after simulating an instruction on counter $i$, so that both counters are zero at the same time only at the halting instruction. In both cases the run is stopped with probability $1$ if the machine halts and with probability $0$ otherwise. The constructions adapt to higher dimensions.

## Sources

- T. Brázdil, S. Kiefer, A. Kučera, P. Novotný and J.-P. Katoen, "Zero-reachability in probabilistic multi-counter automata", in *Proceedings of the Joint Meeting of the Twenty-Third EACSL Annual Conference on Computer Science Logic (CSL) and the Twenty-Ninth Annual ACM/IEEE Symposium on Logic in Computer Science (LICS)*, ACM, 2014, pp. 1–10, doi:10.1145/2603088.2603161; read as arXiv:1401.6840v1, <https://arxiv.org/abs/1401.6840v1>: Observation 1 (undecidability of qualitative $\mathcal{Z}$-reachability under conditions 1 and 2) with its proof, Definition 2 (probabilistic multi-counter automata) and the definitions of stopping criteria and the qualitative $\mathcal{Z}$-reachability problem in the preliminaries, in the numbering of that version.
