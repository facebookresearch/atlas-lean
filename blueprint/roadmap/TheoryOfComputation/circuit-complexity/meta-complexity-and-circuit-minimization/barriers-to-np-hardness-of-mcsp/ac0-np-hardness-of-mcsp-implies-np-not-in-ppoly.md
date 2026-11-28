# Uniform AC0 NP-hardness of MCSP implies NP is not in P/poly

If MCSP is NP-hard under logtime-uniform $\mathrm{AC}^0$ reductions, then $\mathrm{NP}\not\subseteq\mathrm{P/poly}$ and E requires circuits of size $2^{\delta n}$ almost everywhere for some $\delta>0$, so $\mathrm{P}=\mathrm{BPP}$.

**Theorem (Murray–Williams).** If MCSP is NP-hard under logtime-uniform $\mathrm{AC}^0$ reductions, then $\mathrm{NP}\not\subseteq\mathrm{P/poly}$ and $\mathrm{E}\not\subseteq\text{i.o.-}\mathrm{SIZE}(2^{\delta n})$ for some $\delta>0$. As a consequence $\mathrm{P}=\mathrm{BPP}$.

The two conclusions come from two separate statements:

- if MCSP is NP-hard under logtime-uniform $\mathrm{AC}^0$ reductions, then $\mathrm{NP}\subseteq\mathrm{P/poly}$ implies $\mathrm{NEXP}\subseteq\mathrm{P/poly}$;
- if MCSP is NP-hard under P-uniform $\mathrm{AC}^0$ reductions, then there is $\delta>0$ with $\mathrm{E}\not\subseteq\text{i.o.-}\mathrm{SIZE}(2^{\delta n})$, and then $\mathrm{P}=\mathrm{BPP}$ by Impagliazzo and Wigderson.

Here $\text{i.o.-}\mathrm{SIZE}(s)$ is the class of languages that have circuits of size $s(n)$ for infinitely many $n$. A reduction is *P-uniform* $\mathrm{AC}^0$ if a polynomial-time algorithm produces its $n$-input circuit from $1^n$, and *logtime-uniform* $\mathrm{AC}^0$ if, in the standard sense, the connections and gate types of its circuits are decidable in time logarithmic in the circuit size. Neither is the log-space uniformity of the linked uniform-family page, which supplies only the notion of a uniform circuit family.

## Expansion

For the first statement, pad a language $L\in\mathrm{NTIME}(2^{n^c})$ into the sparse NP language $\{x01^{t} : x\in L,\ t=2^{|x|^c}\}$ and apply the uniform $\mathrm{AC}^0$ reduction. Each output bit is then computable in $\Sigma_k\mathrm{P}$, hence in P/poly under the hypothesis, so the produced exponential-size truth tables have polynomial-size circuits; a $\Sigma_{k+2}\mathrm{P}$ machine guesses a small circuit for the instance and checks it, giving $\mathrm{NEXP}\subseteq\Sigma_{k+2}\mathrm{P}\subseteq\mathrm{P/poly}$. For the second, P-uniform $\mathrm{AC}^0$ hardness gives P-uniform $\mathrm{NC}^0$ hardness (Agrawal et al.), the $\mathrm{NC}^0$ reduction from PARITY is made natural, and if E had circuits of size $2^{\varepsilon n}$ infinitely often for every $\varepsilon>0$, the size parameters and produced truth tables would be small enough to give depth-three circuits of size $2^{\tilde O(n^{\gamma})}$ for PARITY for every $\gamma>0$ at infinitely many lengths, contradicting Håstad's depth-$d$ bound. The resulting worst-case hardness of E at almost every length gives $\mathrm{P}=\mathrm{BPP}$ by Impagliazzo and Wigderson.


Known unstated proof prerequisites needed before this node is ready for formalization:

- Agrawal et al. reduction from P-uniform AC0 hardness to P-uniform NC0 hardness (Agrawal–Allender–Impagliazzo–Pitassi–Rudich, *Computational Complexity* 10(2), 2001, Theorem 4.1, used in the proof of Murray–Williams Theorem 4.4)

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Uniform circuit families](../../../complexity-classes/time-and-space-complexity-classes/uniform-circuit-family.md)
- [AC0](../../../complexity-classes/time-and-space-complexity-classes/ac0.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [Polynomial time with polynomial advice](../../../complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [The class E](../../../complexity-classes/time-and-space-complexity-classes/e.md)
- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [The complexity class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [The complexity class NEXP](../../../complexity-classes/time-and-space-complexity-classes/nexp.md)

## Proof depends on

- [Depth-d circuit size of parity](../../lower-bounds-for-ac0-circuits/depth-d-circuit-size-of-parity.md)
- [Impagliazzo-Wigderson: exponential circuit hardness in E derandomizes BPP](../../../pseudorandomness-and-one-way-functions/nisan-wigderson.md)

## Sources

- Cody D. Murray, R. Ryan Williams, "On the (Non) NP-Hardness of Computing Circuit Complexity", *Theory of Computing* 13(4), 2017, https://doi.org/10.4086/toc.2017.v013a004 (Theorem 1.8, Theorems 4.3 and 4.4, Lemma 2.3).
