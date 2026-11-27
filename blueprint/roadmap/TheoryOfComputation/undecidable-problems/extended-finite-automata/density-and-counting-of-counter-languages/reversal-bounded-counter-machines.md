# Reversal-bounded counter machines

A one-way counter machine is a finite automaton reading its input left to right with a fixed number of counters over the natural numbers that it can increment, decrement and test for zero; it is $l$-reversal-bounded if in every accepting computation each counter alternates between increasing and decreasing at most $l$ times.

**Definition.** A *one-way $k$-counter machine* is a tuple $M = (k, Q, \Sigma, \lhd, \delta, q_0, F)$ with a finite set $Q$ of states, an input alphabet $\Sigma$, a right end-marker $\lhd$, an initial state $q_0$, accepting states $F \subseteq Q$, and a transition relation $\delta$ from $Q \times (\Sigma \cup \{\lhd\}) \times \{0, 1\}^k$ to $Q \times \{\mathrm{S}, \mathrm{R}\} \times \{-1, 0, +1\}^k$. A transition reads the current input symbol and the zero/nonzero status of each counter, moves to a new state, keeps the input head in place ($\mathrm{S}$) or moves it right ($\mathrm{R}$), and adds $-1$, $0$ or $+1$ to each counter, never decrementing a counter that is zero. A word $w$ is accepted if from $(q_0, w\lhd, 0, \dots, 0)$ the machine can reach a configuration with an accepting state and only $\lhd$ left to read; $L(M)$ is the set of accepted words. The machine is *deterministic* if $\delta$ is a partial function, and *$l$-reversal-bounded* if in every accepting computation each counter alternates between increasing and decreasing at most $l$ times.

The classes used for undecidability results are:

- $\mathrm{NCM}(k, l)$ and $\mathrm{DCM}(k, l)$: languages of nondeterministic, respectively deterministic, one-way $l$-reversal-bounded $k$-counter machines, and $\mathrm{NCM}$, $\mathrm{DCM}$ their unions over $k, l$;
- $\mathrm{NCA}$: languages of nondeterministic one-way one-counter machines with no bound on reversals;
- *real-time* machines, which move the input head right at every step.

A counter making $l \ge 1$ reversals can be simulated by $\lceil (l+1)/2 \rceil$ counters making one reversal each, so for instance $\mathrm{DCM}(1, 3) \subseteq \mathrm{DCM}(2, 1)$. Emptiness and, for deterministic machines, universality and inclusion are decidable for these classes (Ibarra), while universality is undecidable for $\mathrm{NCM}(1, 1)$ (a classical result quoted in the source).

## Depends on

None.

## Proof depends on

None.

## Sources

- J. Eremondi, O. H. Ibarra and I. McQuillan, "On the Density of Context-Free and Counter Languages", *International Journal of Foundations of Computer Science* 29(2):233–250, 2018, doi:[10.1142/S0129054118400051](https://doi.org/10.1142/S0129054118400051); numbering of arXiv:1903.03001v1: the definition of one-way $k$-counter machines, reversal-boundedness and the classes $\mathrm{NCM}(k,l)$, $\mathrm{DCM}(k,l)$ and $\mathrm{NCA}$ in Section 2, and the remarks on universality in Section 1.
- O. H. Ibarra, I. McQuillan and B. Ravikumar, "On counting functions and slenderness of languages", *Theoretical Computer Science* 777:356–378, 2019, doi:[10.1016/j.tcs.2018.11.021](https://doi.org/10.1016/j.tcs.2018.11.021); numbering of arXiv:1903.03504v1: the real-time machines used in Section 5.
