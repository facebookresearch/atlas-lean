# General no-cloning with environment and no-broadcasting

This node collects the mixed-state generalizations of the no-cloning theorem. In the model of the
cited source, a system $A$ prepared in one of two states $\rho_0, \rho_1$ is joined with an ancilla
$B$ in a fixed standard state and an environment $C$ in a fixed state, and a unitary acts on $ABC$;
every quantum channel arises this way.

## Expansion

A sound expansion has separate pages for:

1. **No-broadcasting.** The pair $\{\rho_0, \rho_1\}$ can be broadcast, that is, some such evolution
   yields a state of $AB$ whose two marginals both equal $\rho_s$ when the input is $\rho_s$ for
   $s = 0, 1$, if and only if $\rho_0 \rho_1 = \rho_1 \rho_0$.
2. **Mixed-state no-cloning.** The pair can be cloned, that is, mapped to $\rho_s \otimes \rho_s$, if
   and only if $\rho_0 = \rho_1$ or $\rho_0 \rho_1 = 0$. In particular two pure states with
   $0 < \lvert \langle \psi_0, \psi_1 \rangle \rvert < 1$ can be neither cloned nor broadcast by any
   channel, with any environment.
3. The equivalence between the unitary-with-environment model and arbitrary channels (Stinespring
   dilation), stated as its own page.

The pure-state unitary case of item 2 for two states is a separate page (see Related topics); it is a special case, not a proof input for mixed states.

- Statement prerequisite: quantum channels (completely positive trace-preserving maps) and their Stinespring dilation.

## Proof depends on

- [Monotonicity of fidelity under channels](../quantum-operations/monotonicity-of-fidelity-under-channels.md)

## Related topics

- [No-cloning theorem for two states](../quantum-operations/no-cloning-two-state.md): the pure-state unitary special case.

## Sources

- H. Barnum, C. M. Caves, C. A. Fuchs, R. Jozsa and B. Schumacher, *Noncommuting mixed states cannot
  be broadcast*, Physical Review Letters 76 (1996); arXiv:quant-ph/9511010 (main theorem: broadcasting
  is possible if and only if the states commute; cloning if and only if they are identical or
  orthogonal). <https://arxiv.org/abs/quant-ph/9511010>
