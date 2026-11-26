# Deterministic parity specifications

For types $Q$ (states), $I$ (input letters) and $O$ (output letters), a deterministic parity specification consists of

- an initial state $q_0 \in Q$;
- a deterministic transition function $\delta : Q \times I \times O \to Q$, reading one input/output letter pair per step;
- a priority function $\Omega : Q \to \mathbb{N}$.

No finiteness of $Q$, $I$ or $O$ is part of the definition.
