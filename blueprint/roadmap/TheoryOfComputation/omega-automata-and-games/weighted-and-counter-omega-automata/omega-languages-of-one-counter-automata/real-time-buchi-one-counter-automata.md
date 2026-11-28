# Real-time Büchi one-counter automata

A real-time Büchi one-counter automaton reads an infinite word one letter per step, with finitely many states and a nonnegative counter that it can test for zero and change by one, and accepts when some run visits an accepting state infinitely often.

Let $k\ge1$. A *$k$-counter machine* is a tuple $(K,\Sigma,\Delta,q_0)$ with a finite set $K$ of states, a finite input alphabet $\Sigma$, an initial state $q_0$ and a transition relation $\Delta\subseteq K\times(\Sigma\cup\{\lambda\})\times\{0,1\}^k\times K\times\{0,1,-1\}^k$; a configuration is $(q,c_1,\dots,c_k)$ with $c_i\in\mathbb N$. A transition $(q,a,i_1,\dots,i_k,q',j_1,\dots,j_k)$ applies when each $c_m$ is zero exactly if $i_m=0$, and it adds $j_m$ to $c_m$; a counter tested zero is never decremented. The machine is *real time* if none of its transitions reads $\lambda$, so that it reads one letter per step.

A *Büchi $k$-counter automaton* is $(K,\Sigma,\Delta,q_0,F)$ with $F\subseteq K$. A run on $\sigma\in\Sigma^\omega$ starts in $(q_0,0,\dots,0)$ and reads all of $\sigma$; it is accepting if some state of $F$ occurs infinitely often, and $L(\mathcal M)\subseteq\Sigma^\omega$ is the set of infinite words with an accepting run. One-counter automata are pushdown automata with stack alphabet $\{Z_0,A\}$, $Z_0$ marking the bottom, so their $\omega$-languages are context-free $\omega$-languages (accepted by Büchi pushdown automata).

**Decision problems.** Fix the alphabet $\Omega=\{a,b,E,A,B,F,0\}$ and an effective enumeration $(\mathcal C_z)_{z\in\mathbb N}$ of the real-time Büchi one-counter automata over $\Omega$. A decision problem about these automata is the set of indices $z$ (or pairs $(y,z)$) of the instances with the given property, located in the [analytical hierarchy](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md). *Universality* is $L(\mathcal C_z)=\Omega^\omega$; *regularity* is that $L(\mathcal C_z)$ is $\omega$-regular; *complementability* that $\Omega^\omega\setminus L(\mathcal C_z)$ is $L(\mathcal C_y)$ for some $y$; *determinizability* that $L(\mathcal C_z)=L(\mathcal C_y)$ for some deterministic $\mathcal C_y$; *unambiguity* that $L(\mathcal C_z)=L(\mathcal C_y)$ for some $\mathcal C_y$ having at most one accepting run on each word.

## Depends on

- [Analytical hierarchy](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)
- [Pushdown automaton](../../../context-free-languages/grammars-and-pushdown-automata/pushdown-automata/pda.md)

## Proof depends on

None.

## Expansion

Runs of a real-time one-counter automaton can be coded by infinite binary words, and being an accepting run on a given word is arithmetical, so universality, inclusion and the other problems above lie in $\Pi^1_2$: a universal quantifier over infinite words followed by an existential quantifier over runs. Their $\Pi^1_2$-hardness is inherited from Turing machines on infinite words through effective codings.

## Sources

- Olivier Finkel, "Highly Undecidable Problems For Infinite Computations", *RAIRO - Theoretical Informatics and Applications* 43(2), 2009, pp. 339–364, doi:[10.1051/ita/2009001](https://doi.org/10.1051/ita/2009001); read in arXiv:0901.0373v1 ([arXiv](https://arxiv.org/abs/0901.0373v1)), whose numbering is used: Section 3, Definitions 3.4 and 3.5 (counter machines, real-time machines, Büchi counter automata), the remark on pushdown automata, and the conventions fixing $\Omega$ and the enumeration $(\mathcal C_z)$ before Theorem 3.9.
