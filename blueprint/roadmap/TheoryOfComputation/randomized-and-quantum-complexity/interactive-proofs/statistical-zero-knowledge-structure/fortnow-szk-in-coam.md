# Fortnow: SZK ⊆ coAM

Every promise problem in $\mathsf{SZK}$ (indeed in $\mathsf{HVSZK}$) has a constant-round Arthur–Merlin protocol for its complement: $\mathsf{SZK}\subseteq\mathsf{coAM}$, where $\mathsf{AM}$ denotes two-round public-coin interactive proofs with a polynomial-time verifier.

## Proof sketch

Fortnow's original proof analyzes the simulator directly: on NO instances the simulated conversations must deviate from any real interaction, which is detectable by approximate lower bounds on set sizes in the style of Goldwasser–Sipser. Via completeness of statistical difference one obtains a direct proof: the two-message private-coin protocol in which Arthur picks a hidden bit $b$, sends a sample of $C_b$, and Merlin must guess $b$ proves that two circuits are far apart, so $\mathrm{SD} \in \mathsf{IP}(2) \subseteq \mathsf{AM}$ by Goldwasser–Sipser. Since $\mathsf{SZK}$ is closed under complement, $\overline{\mathrm{SD}}$ Karp-reduces to $\mathrm{SD}$, so $\overline{\mathrm{SD}} \in \mathsf{AM}$, i.e. $\mathrm{SD} \in \mathsf{coAM}$, and completeness of $\mathrm{SD}$ gives $\mathsf{SZK} \subseteq \mathsf{coAM}$.

## Depends on

- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](promise-szk-and-hvszk.md)
- [The class coAM](../../../complexity-classes/time-and-space-complexity-classes/co-am.md)
- [The class $\mathsf{AM}$ (Arthur–Merlin)](../../../complexity-classes/time-and-space-complexity-classes/am.md)

## Proof depends on

- [Okamoto: public-coin HVSZK equals HVSZK](okamoto-public-coin-hvszk-equals-hvszk.md)
- [Okamoto: SZK is closed under complement](okamoto-szk-closed-under-complement.md)
- [Goldwasser-Sipser: private coins add no power to interactive proofs](../../goldwasser-sipser-theorem/goldwasser-sipser.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- Lance Fortnow, "The Complexity of Perfect Zero-Knowledge", STOC (1987); Advances in Computing Research 5 (1989).
- Amit Sahai and Salil Vadhan, "A Complete Problem for Statistical Zero Knowledge", Journal of the ACM 50(2) (2003), ECCC TR00-084.
