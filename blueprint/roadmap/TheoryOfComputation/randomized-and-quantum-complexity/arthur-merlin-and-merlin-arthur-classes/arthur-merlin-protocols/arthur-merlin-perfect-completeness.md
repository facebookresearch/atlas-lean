# MA and AM with perfect completeness

The classes $\mathsf{MA}$ and $\mathsf{AM}$ are unchanged if completeness $2/3$ and soundness $1/3$ are replaced by completeness $1$ and soundness $1/2$: $\mathsf{MA}=\mathsf{MA}_1$ and $\mathsf{AM}=\mathsf{AM}_1$. Moreover, Merlin–Arthur with perfect soundness (no false acceptances) equals $\mathsf{NP}$.

## Proof sketch

Amplify the error to $2^{-m}$ and apply the Lautemann covering argument: Merlin supplies, together with his message, shifts $s_1,\dots,s_m$ such that for every random string $r$ some $r\oplus s_i$ is accepting. On yes-instances such shifts exist by a union bound; on no-instances the covering fails for most $r$. With perfect soundness, any accepted random string is an NP witness.

## Depends on

- [Public-coin Arthur–Merlin games with a fixed move pattern](arthur-merlin-move-patterns.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Sipser-Gács-Lautemann: BPP is in $\Sigma_2^p$ and $\Pi_2^p$](../../sipser-gacs-lautemann.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 6–7", 2007, Exercise 6.12.
- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 9–10", 2007, Exercises 9.8 and 9.9.
