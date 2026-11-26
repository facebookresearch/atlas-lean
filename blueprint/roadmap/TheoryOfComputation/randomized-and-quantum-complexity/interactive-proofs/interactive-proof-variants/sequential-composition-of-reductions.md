# Sequential composition of interactive reductions

If $\Pi_1$ is an interactive reduction from $R_1$ to $R_2$ and $\Pi_2$ one from $R_2$ to $R_3$, their concatenation $\Pi_1\circ\Pi_2$ is a reduction from $R_1$ to $R_3$ with rounds the concatenation of the rounds. Completeness, soundness, knowledge soundness and round-by-round (knowledge) soundness are preserved, the round-by-round errors of the composition being the concatenated error lists (so total error the sum).

## Proof sketch

Run the two protocols in sequence; define the doomed predicate of the composition as that of $\Pi_1$ on its prefix, switching to that of $\Pi_2$ (applied to $\Pi_1$'s output statement) afterwards; the extractor of the composition composes the two extractors backwards.

## Depends on

- [Interactive reductions and round-by-round (knowledge) soundness](round-by-round-knowledge-soundness.md)

## Sources

- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024.
- Eli Ben-Sasson, Alessandro Chiesa and Nicholas Spooner, "Interactive Oracle Proofs", Theory of Cryptography – TCC 2016-B, Part II, 2016.
