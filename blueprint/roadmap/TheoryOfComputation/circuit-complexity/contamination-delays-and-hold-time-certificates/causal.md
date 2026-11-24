# Causal gate-delay model for one gate, after the clock edge

The gate
reading `line` has nonnegative contamination delay `cdelay` and output signal
`out`: whenever every wire it reads is stable on `[0, τ)`, its output is stable
on `[0, cdelay + τ)`. A gate with no inputs is therefore constant after the
edge. Only times from the edge at `0` on are constrained: this does not say the
output had settled before the edge (see `SettledBefore`).
