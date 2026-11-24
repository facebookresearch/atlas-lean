# `jz r j` is URM `J r z j` against a zero register

Where the counter
program has `jz r j`, a URM program has `J r z j` at the current program counter,
and register `z` holds `0`, one counter step is one CSLib `URM.Step`.
