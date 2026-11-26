# SZK cannot contain NP unless the polynomial hierarchy collapses to its second level

If $\mathsf{NP}\subseteq\mathsf{SZK}$ (for instance, if some $\mathsf{SZK}$ problem is $\mathsf{NP}$-hard under polynomial-time Karp reductions), then $\mathsf{PH}=\Sigma_2^{p}=\Pi_2^{p}$. Hence natural $\mathsf{SZK}$ problems such as graph isomorphism, quadratic residuosity, statistical difference and entropy difference are not $\mathsf{NP}$-hard unless the polynomial hierarchy collapses.

## Proof sketch

From $\mathsf{SZK}\subseteq\mathsf{coAM}$ one gets $\mathsf{NP}\subseteq\mathsf{coAM}$, i.e. $\mathsf{coNP}\subseteq\mathsf{AM}$. Recall the Boppana–Håstad–Zachos theorem: $\mathsf{coNP}\subseteq\mathsf{AM}$ implies $\Sigma_2^p\subseteq\mathsf{AM}\subseteq\Pi_2^p$, so $\Sigma_2^p=\Pi_2^p$ and the hierarchy collapses to its second level.

## Depends on

- [Aiello–Håstad: SZK ⊆ AM, hence SZK ⊆ AM ∩ coAM](aiello-hastad-szk-in-am.md)
- [Collapse of the polynomial hierarchy to a level](../../../complexity-classes/polynomial-hierarchy/collapse-of-the-polynomial-hierarchy-to-a-level.md)

## Proof depends on

- [Fortnow: SZK ⊆ coAM](fortnow-szk-in-coam.md)
- [AM is contained in $\Pi_2^p$ (Babai)](../../arthur-merlin-and-merlin-arthur-classes/am-subset-pi2.md)
- [Collapse of the polynomial hierarchy to a level](../../../complexity-classes/polynomial-hierarchy/collapse-of-the-polynomial-hierarchy-to-a-level.md)

## Sources

- Lance Fortnow, "The Complexity of Perfect Zero-Knowledge", STOC (1987); Advances in Computing Research 5 (1989).
- William Aiello and Johan Håstad, "Statistical Zero-Knowledge Languages Can Be Recognized in Two Rounds", Journal of Computer and System Sciences 42(3) (1991).
- Amit Sahai and Salil Vadhan, "A Complete Problem for Statistical Zero Knowledge", Journal of the ACM 50(2) (2003), ECCC TR00-084.
