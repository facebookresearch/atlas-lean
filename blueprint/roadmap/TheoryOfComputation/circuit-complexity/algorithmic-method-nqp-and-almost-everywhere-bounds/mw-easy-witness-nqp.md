# Murray–Williams easy witness lemma for NQP and NP

There is an absolute constant $c \ge 1$ such that for every $k \ge 1$: if $\mathrm{NQP} = \bigcup_j \mathrm{NTIME}[2^{\log^j n}] \subseteq \mathrm{SIZE}[2^{\log^k n}]$, then every language $L \in \mathrm{NQP}$ (for every verifier) has witness circuits of size $2^{c \log^{k^3} n}$ (Murray–Williams, Lemma 1.3). As a corollary, if $\mathcal{C}$ is a typical circuit class (evaluatable and closed under negation and conjunctions, §1.1) and $\mathrm{NQP} \subseteq \mathcal{C}\text{-}\mathrm{SIZE}[2^{\log^k n}]$, then because the circuit value problem lies in $\mathrm{P} \subseteq \mathrm{NQP}$ and hence has $2^{\log^k n}$-size $\mathcal{C}$-circuits, composing a general witness circuit with a $\mathcal{C}$-circuit evaluator gives quasi-polynomial-size $\mathcal{C}$-circuit witnesses for every $\mathrm{NQP}$ verifier. The scaled-down version holds as well: if $\mathrm{NP} \subseteq \mathrm{SIZE}[n^k]$ for a fixed $k$, then every $\mathrm{NP}$ verifier has witnesses with circuits of size $n^{O(k^3)}$.

## Proof sketch

Assume a verifier has no small-circuit witnesses on infinitely many inputs. Using the non-witnessable instances as advice-free hardness, construct a pseudorandom generator against circuits of a fixed polynomial size computable in nondeterministic time; combined with the circuit upper bound assumption for the whole $\mathrm{NQP}$ hierarchy, a careful parameter accounting (rather than the exponential-time diagonalization of the original easy witness lemma) yields that some language in $\mathrm{NTIME}[n^{\log^{k+1} n}]$ lacks small circuits, contradicting the assumption.

## Depends on

- [Nondeterministic quasi-polynomial time](nqp-class.md)

## Proof depends on

- [Impagliazzo–Kabanets–Wigderson easy witness lemma for NEXP](easy-witness-ikw.md)

## Sources

- C. Murray, R. Williams, "Circuit lower bounds for nondeterministic quasi-polytime: an easy witness lemma for NP and NQP", STOC (2018); SIAM Journal on Computing 49 (2020).
