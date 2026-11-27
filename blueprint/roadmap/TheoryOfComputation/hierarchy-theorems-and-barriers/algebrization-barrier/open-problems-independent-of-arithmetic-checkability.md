# Open problems independent of arithmetic checkability

Arithmetic checkability, even in its strong form, cannot settle $\mathsf{P}$ versus $\mathsf{NP}$, $\mathsf{P}$ versus $\mathsf{BPP}$, explicit exponential circuit lower bounds or $\mathsf{BQP}$ versus $\mathsf{BPP}$, and it also fails to prove the true statement $\mathsf{E}\subseteq\mathsf{MIP}$.

Say that the theory $\mathrm{ACT}^*$ implies a complexity statement if the statement holds relative to every oracle consistent with the strong arithmetic checkability axiom $\mathsf{P}=\mathsf{ALG}\text{-}\mathsf{PF}^*$. Then $\mathrm{ACT}^*$ implies none of the following:

1. $\mathsf{P}\ne\mathsf{PSPACE}$, and hence not $\mathsf{P}\ne\mathsf{NP}$;
2. $\mathsf{E}\subseteq\mathrm{io}\text{-}\mathrm{SIZE}(2^{n/4})$;
3. $\mathsf{E}\subseteq\mathsf{MIP}$;
4. $\mathsf{NP}\subseteq\mathrm{io}\text{-}\mathrm{SIZE}(2^{n/4})$, which with item 1 gives independence of both $\mathsf{NP}=\mathsf{P}$ and $\mathsf{NP}\subseteq\mathsf{BPP}$;
5. "$\mathsf{BPP}\ne\mathsf{P}$ or $\mathsf{P}=\mathsf{NP}$";
6. $\mathsf{BPP}\subseteq\mathsf{DTIME}(2^{o(n)})$;
7. $\mathsf{EXP}\not\subseteq\mathrm{io}\text{-}\mathsf{P}/\mathrm{poly}$;
8. $\mathsf{coNP}\subseteq\mathsf{MA}$, $\mathsf{NP}\subseteq\mathsf{BQP}$, $\mathsf{BQP}\subseteq\mathsf{BPP}$ and $\mathsf{QMA}\subseteq\mathsf{MA}$.

Item 5 is a compound statement, beyond the single inclusions and separations that the Aaronson–Wigderson definition of algebrization covers. Since provability from $\mathrm{ACT}$ is closed under deduction, these independence results are immune to the modus ponens concern raised for algebrization.

## Expansion

Items 1 to 3 use self-algebrizing encodings: for a $\mathsf{PSPACE}$-complete $L$, its self-algebrizing encoding $A$ is consistent with $\mathrm{ACT}^*$ and satisfies $\mathsf{P}^A=\mathsf{PSPACE}^A$; padding gives $\mathsf{E}^A=\mathsf{SPACE}^A(2^{O(n)})$, which escapes $\mathrm{io}\text{-}\mathrm{SIZE}^A(2^{n/4})$ by counting; and diagonalizing an oracle $L$ with $\mathsf{E}^L\not\subseteq\mathsf{MIP}^{\mathsf{PSPACE}^L}$ before encoding gives item 3. The remaining items reduce to communication complexity lower bounds, using that the disjoint union $A_0+A_1$ of two oracles consistent with $\mathrm{ACT}^*$ is again consistent, so that two players holding $A_0$ and $A_1$ must simulate any algorithm with access to $A_0+A_1$. Items 5 and 7 then follow from items 4 and 6 because hardness-randomness tradeoffs relativize.

## Depends on

- [Arithmetic checkability axiom](arithmetic-checkability-axiom.md)

## Proof depends on

- [Aaronson-Wigderson: the algebrization barrier](aaronson-wigderson-algebrization.md)
- [Baker-Gill-Solovay: oracles separate and collapse P vs NP](../relativization-and-oracle-separations/baker-gill-solovay.md)

## Sources

- Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "An Axiomatic Approach to Algebrization", *Proceedings of the 41st ACM Symposium on Theory of Computing (STOC 2009)*, 2009, https://doi.org/10.1145/1536414.1536509 (Theorems 4.1 and 4.2, Lemma 4.3, Section 4).
