# Nominal automata and residual nominal automata

Nominal automata generalize finite automata to infinite alphabets of data values by replacing finite sets with orbit-finite
nominal sets; a nominal automaton is residual if every state accepts a derivative of the language of the automaton.

**Nominal sets.** Let $\mathbb{A}$ be a countably infinite set of *atoms* and $\mathrm{Perm}(\mathbb{A})$ the group of finite
permutations of $\mathbb{A}$, those moving only finitely many atoms. A set $X$ with a group action of $\mathrm{Perm}(\mathbb{A})$ is a
*nominal set* if every $x \in X$ has a finite *support*, a finite set $A \subseteq \mathbb{A}$ such that $\pi x = x$ for every
permutation $\pi$ fixing $A$ pointwise; $\mathrm{supp}(x)$ is the least support. A subset, relation or function is *equivariant* if it
is supported by the empty set. The *orbit* of $x$ is $\{\pi x : \pi \in \mathrm{Perm}(\mathbb{A})\}$, and $X$ is *orbit-finite* if it is a
finite union of orbits. Orbit-finite sets have finite representations.

**Automata.** A *nondeterministic nominal automaton* $\mathcal{A} = (\Sigma, Q, I, F, \delta)$ has an orbit-finite nominal alphabet
$\Sigma$, an orbit-finite nominal set $Q$ of states, and equivariant subsets $I \subseteq Q$ of initial states, $F \subseteq Q$ of final
states and $\delta \subseteq Q \times \Sigma \times Q$ of transitions. Acceptance is defined as for finite automata; $\mathcal{L}(\mathcal{A})$ is
the language of $\mathcal{A}$ and $\mathcal{L}(q)$ the language accepted from a state $q$. For a language $L$ and a word $u$, the
*derivative* is $u^{-1} L = \{ w : uw \in L \}$. The automaton is

- *deterministic* if $I = \{q_0\}$ and every pair $(q, a)$ admits a unique successor;
- *residual* if for each state $q$ there is a word $w \in \Sigma^*$ with $\mathcal{L}(q) = w^{-1} \mathcal{L}(\mathcal{A})$;
- *non-guessing* if $\mathrm{supp}(q_0) = \emptyset$ for every initial state $q_0$ and $\mathrm{supp}(q') \subseteq \mathrm{supp}(q) \cup \mathrm{supp}(a)$
  for every transition $(q, a, q')$.

Unlike finite automata, nondeterministic nominal automata accept more languages than deterministic ones, and their universality
problem is undecidable, even for non-guessing automata (Bojańczyk); universality of residual nominal automata is decidable.

## Depends on

None.

## Proof depends on

None.

## Sources

- J. Moerman and M. Sammartino, "Residuality and learning for nondeterministic nominal automata", *Logical Methods in Computer Science* 18(1), paper 29, 2022, doi:10.46298/lmcs-18(1:29)2022; numbering of the version arXiv:1910.11666v7: Section 2.1 (nominal sets), Definitions 2.4 (nominal automata), 2.6 (derivatives) and 2.7 (deterministic, residual and non-guessing automata), and Proposition 5.1 (universality of residual automata is decidable).
- A. M. Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013 (nominal sets and supports).
