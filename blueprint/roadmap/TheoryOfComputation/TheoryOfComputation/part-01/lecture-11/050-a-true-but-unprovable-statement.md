---
article_id: af_4862956eeda37da8ca76f430
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: GodelIncompleteness.true_but_unprovable_statement
---

# Theorem (A True but Unprovable Statement)

(1) $\varphi_U$ has no proof. (2) $\varphi_U$ is true. Where $\varphi_U$ is the statement $\langle R, 0 \rangle \in \overline{A_{\mathrm{TM}}}$ and $R$ is a TM that on any input obtains $\langle R \rangle$, uses it to obtain $\varphi_U$, and for each possible proof $\pi$ tests if $\pi$ is a proof that $\varphi_U$ is true, accepting if yes.

## Depends on

- [Definition: Turing Machine](../lecture-5/022-definition-turing-machine.md)
- [Definition: Decider](../lecture-5/024-definition-decider.md)

## Proof depends on

- [Theorem (Recursion Theorem)](045-recursion-theorem.md)

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 11, A True but Unprovable Statement section](../../../../../sources/v1/TheoryOfComputation.md)
