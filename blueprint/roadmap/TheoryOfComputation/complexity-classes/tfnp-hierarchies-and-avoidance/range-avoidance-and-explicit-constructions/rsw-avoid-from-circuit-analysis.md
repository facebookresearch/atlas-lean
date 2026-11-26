# Ren–Santhanam–Wang: FP^NP algorithms for C-Avoid from circuit-analysis data structures

Generalizing Williams's connection between circuit-analysis algorithms and circuit lower bounds: for a multi-output circuit class $\mathcal{C}$ (under mild closure properties), if Hamming-weight estimation for $\mathrm{NC}^0\circ\mathcal{C}$ circuits with $\ell$ outputs has a data structure with $\mathrm{P}^{\mathrm{NP}}$ preprocessing and query time $\ell/\log^{\omega(1)}\ell$, then $\mathcal{C}$-Avoid is in $\mathrm{FP}^{\mathrm{NP}}$ for a stretch determined by the data structure, which is at best $\ell(n)=n^{1+\epsilon}$ for a constant $\epsilon>0$. As an application, for every polynomial $s=s(n)$ there is an $\mathrm{FP}^{\mathrm{NP}}$ algorithm that, given $C\colon\{0,1\}^n\to\{0,1\}^{\ell}$ with $\ell\ge n^{\omega(\sqrt{s}\log s)}$ in which each output bit is computed by a De Morgan formula of size $s$, outputs a string outside the range of $C$. A key ingredient is a construction of rectangular PCPs of proximity, building on rectangular PCPs of Bhangale, Harsha, Paradise and Tal.

## Proof sketch

Encode the candidate non-image as a PCP of proximity for the statement that it is in the range; rectangularity lets a data structure for $\mathcal{C}$ evaluate all verifier queries on the given circuit faster than brute force. An $\mathrm{NP}$ oracle then builds a string bit by bit, and a successful fast analysis certifies that the string has no preimage.

## Depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)

## Proof depends on

- [Williams: NEXP is not contained in ACC0](../../../circuit-complexity/williams-nexp-not-in-acc0.md)

## Sources

- Hanlin Ren, Rahul Santhanam and Zhikun Wang, "On the Range Avoidance Problem for Circuits", FOCS (2022), ECCC TR22-048.
