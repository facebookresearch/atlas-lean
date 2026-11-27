# Murray–Williams easy witness lemma for NQP and NP

Let $\mathcal{C}$ be a typical circuit class (closed under composition with $\mathrm{AC}^0$). If $\mathrm{NTIME}[n^{\log^{k} n}] \subseteq \mathcal{C}$-$\mathrm{SIZE}[\operatorname{poly}(n)]$ for every $k$, then every $\mathrm{NQP} = \bigcup_k \mathrm{NTIME}[2^{\log^k n}]$ verifier has witnesses whose truth tables are computed by $\mathcal{C}$-circuits of quasi-polynomial size. The scaled-down version holds as well: if $\mathrm{NP} \subseteq \mathrm{SIZE}[n^k]$ for a fixed $k$, then every $\mathrm{NP}$ verifier has witnesses with circuits of size $n^{O(k^3)}$.

## Proof sketch

Assume a verifier has no small-circuit witnesses on infinitely many inputs. Using the non-witnessable instances as advice-free hardness, construct a pseudorandom generator against circuits of a fixed polynomial size computable in nondeterministic time; combined with the circuit upper bound assumption for the whole $\mathrm{NQP}$ hierarchy, a careful parameter accounting (rather than the exponential-time diagonalization of the original easy witness lemma) yields that some language in $\mathrm{NTIME}[n^{\log^{k+1} n}]$ lacks small circuits, contradicting the assumption.

## Depends on

- [Nondeterministic quasi-polynomial time](nqp-class.md)

## Proof depends on

- [Impagliazzo–Kabanets–Wigderson easy witness lemma for NEXP](easy-witness-ikw.md)

## Sources

- C. Murray, R. Williams, "Circuit lower bounds for nondeterministic quasi-polytime: an easy witness lemma for NP and NQP", STOC (2018); SIAM Journal on Computing 49 (2020).
