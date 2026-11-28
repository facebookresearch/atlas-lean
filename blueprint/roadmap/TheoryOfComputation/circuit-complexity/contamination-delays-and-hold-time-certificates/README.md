# Contamination delays and hold-time certificates

## Signals and the causal gate-delay model

- [Stable before a time](stable-before.md)
- [Causal gate-delay model for one gate, after the clock edge](causal.md)
- [Causal gate-delay model for a program](causal-2.md)
- [Hold check at the receiving register](hold-met.md)
- [Settled before the edge](settled-before.md)
- [Capture check at the receiving register](capture-met.md)

## Earliest change: min-plus propagation of contamination delays

- [Earliest change of a gate](earliest.md)
- [Earliest changes of the gates of a program](earliests.md)
- [Earliest changes of all wires of a program](wire-earliests.md)
- [Earliest changes of the outputs of a circuit](output-earliests.md)

## Line earliest: no-transition constants and min over fan-in

- [Computed earliest change of a gate with no inputs](earliest-of-arity-eq-zero.md)
- [A gate's earliest change is at most its delay plus any input's](earliest-le-add-wire-earliest.md)
- [A common lower bound on the inputs bounds a gate's earliest change](add-le-earliest-of-forall-le.md)

## Program earliest: structural equations

- [The newest gate's earliest change](earliests-gate-last.md)
- [Adding a gate keeps the earlier gates' earliest changes](earliests-gate-cast-succ.md)
- [The earliest change of an input wire](wire-earliests-input.md)

## Time shift and the launch bound

- [Delaying the inputs delays every wire](wire-earliests-add.md)
- [Delaying the inputs delays every output](output-earliests-add.md)
- [No change before launch](le-wire-earliests.md)

## Soundness and the hold certificate

- [Soundness of min-plus propagation](stable-before-wire-earliests.md)
- [Soundness of earliest changes at the outputs](stable-before-output-earliests.md)
- [Hold certificate](hold-met-of-le-output-earliests.md)
- [Capture certificate](capture-met-of-le-output-earliests.md)
