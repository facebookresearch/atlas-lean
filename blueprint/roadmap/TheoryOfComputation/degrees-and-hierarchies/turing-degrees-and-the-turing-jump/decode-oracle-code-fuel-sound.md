# Decoder soundness

Write $\langle a, b \rangle$ for the pairing bijection
$\mathbb{N} \times \mathbb{N} \to \mathbb{N}$ of the Gödel numbering. For every fuel $f$, tag
$t$, payload $p$ and oracle code $c$, if the fuel-indexed decoder with fuel $f$, tag $t$ and
payload $p$ returns $c$, then the Gödel number of $c$ is $\langle t, p \rangle$.

Together with the fact that the fuel-indexed decoder inverts the encoder at any fuel above the
code depth, this says that the decoder is exactly the inverse of the Gödel numbering on its image.

## Sources

- Rogers, *Theory of Recursive Functions and Effective Computability*, §1.6 (Gödel numberings; decoding).
