# Aiello–Håstad: SZK ⊆ AM, hence SZK ⊆ AM ∩ coAM

Every promise problem in $\mathsf{SZK}$ has a two-round Arthur–Merlin protocol: $\mathsf{SZK}\subseteq\mathsf{AM}$. Together with $\mathsf{SZK}\subseteq\mathsf{coAM}$ this gives $\mathsf{SZK}\subseteq\mathsf{AM}\cap\mathsf{coAM}$, and in particular $\mathsf{SZK}\subseteq\Pi_2^{p}\cap\Sigma_2^{p}$.

## Proof sketch

Aiello and Håstad show that the simulator yields a bounded-round protocol in which the prover's role can be emulated within $\mathsf{AM}$, using set lower bound protocols to certify the size of the set of simulated transcripts; a bounded number of rounds then collapses to two by Babai's round reduction. Alternatively, since $\mathsf{SZK}$ is closed under complement, $\mathsf{SZK}\subseteq\mathsf{coAM}$ applied to $\overline\Pi$ gives $\Pi\in\mathsf{AM}$.

## Depends on

- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](promise-szk-and-hvszk.md)
- [The class $\mathsf{AM}$ (Arthur–Merlin)](../../../complexity-classes/time-and-space-complexity-classes/am.md)
- [The class coAM](../../../complexity-classes/time-and-space-complexity-classes/co-am.md)

## Proof depends on

- [Fortnow: SZK ⊆ coAM](fortnow-szk-in-coam.md)
- [Okamoto: SZK is closed under complement](okamoto-szk-closed-under-complement.md)
- [AM is contained in $\Pi_2^p$ (Babai)](../../arthur-merlin-and-merlin-arthur-classes/am-subset-pi2.md)

## Sources

- William Aiello and Johan Håstad, "Statistical Zero-Knowledge Languages Can Be Recognized in Two Rounds", Journal of Computer and System Sciences 42(3) (1991).
- Amit Sahai and Salil Vadhan, "A Complete Problem for Statistical Zero Knowledge", Journal of the ACM 50(2) (2003), ECCC TR00-084.
