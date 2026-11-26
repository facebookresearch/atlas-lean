# Completing submeasurements with a failure outcome

Let $P,R$ be projective measurements with outcome set $\alpha\cup\{\bot\}$ ($\bot$ = failure) in a star-ordered algebra with state $\varphi$. Write the successful effect as $S_P = \sum_{a\in\alpha}P_a$, the successful copy defect as $\sum_{a\in\alpha}\|P_a-R_a\|_\varphi^2$, and similarly the successful pair defect, summed over successful outcome pairs only.

1. If $P_a$ and $R_b$ commute for $a,b\in\alpha$, the full copy defect is at most twice the successful copy defect.
2. For projective $P,Q$ with commuting projective copies $R,T$ (each of $P,Q$ commuting with each of $R,T$), the full pair commutator defect of $P,Q$ is at most $81$ times their successful pair defect plus $8$ times the successful copy defect of $(P,R)$ plus $72$ times that of $(Q,T)$.
3. For commuting measurements $L,R$ with equal successful mass $\operatorname{Re}\varphi(S_L) = \operatorname{Re}\varphi(S_R)$, the disagreement satisfies $1-\sum_{c}\operatorname{Re}\varphi(L_cR_c)\le2\big(\operatorname{Re}\varphi(S_L)-\sum_{a\in\alpha}\operatorname{Re}\varphi(L_aR_a)\big)$.

None of these bounds depends on the size of $\alpha$.

## Proof sketch

The failure effect is $1-S_P$, so its discrepancy is the norm of a sum of successful discrepancies; orthogonality of distinct projective outcomes and commutation with the copy make the cross terms nonpositive, avoiding a factor $|\alpha|$. The commutator bound expands the failure effects the same way and moves factors to the copies. Part 3 counts each successful disagreement on either side at most twice.

## Depends on

- [Sequential projective measurements and their commutator defects](sequential-projective-measurements.md)
- [Measurements, agreement and character observables in a star-ordered algebra](../../../../QuantumInformation/quantum-foundations/states-and-measurements-on-operator-algebras/algebraic-measurements-and-agreement.md)

## Proof depends on

- [Consistent measurements are close in the state](../../../../QuantumInformation/quantum-foundations/states-and-measurements-on-operator-algebras/consistency-implies-closeness.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "Quantum soundness of the classical low individual degree test", arXiv:2009.12982, 2020.
