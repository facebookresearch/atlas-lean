# Quadratic overhead of single-tape simulation

## Multi-stack steps on the `TM1` emulator

- [The emulator walks right to the top of a stack](relates-in-steps-go.md)
- [The emulator walks back to the bottom](relates-in-steps-ret.md)
- [Running one statement on the emulator](exists-relates-in-steps-step-aux.md)
- [One multi-stack step costs at most $1 + B(2(H + B) + 2)$ emulator steps](exists-relates-within-steps-tm1-of-step.md)
- [The emulation halts where the multi-stack machine halts](tm0-step-eq-none-of-step-eq-none.md)

## `TM1` steps on `TM0`

- [Each step of the $\mathrm{TM1}$ emulator is at most three single-tape steps](relates-within-steps-tm0-of-relates-in-s.md)

## Runs of bundled machines

- [Emulation constant](emulation-constant.md)
- [Quadratic overhead of the single-tape emulation](exists-tm0-run-of-tm2-run.md)
- [Single-tape emulation of halting multi-stack runs](exists-tm0-halt-of-tm2-halt.md)
