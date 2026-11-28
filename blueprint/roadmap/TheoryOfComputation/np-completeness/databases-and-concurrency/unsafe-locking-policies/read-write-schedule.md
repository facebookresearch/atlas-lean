# Schedule of reads and writes of `σ` in UNSAFE LOCKING POLICY for two distributed transactions

For an instance `i` of UNSAFE LOCKING POLICY for two distributed transactions, the schedule of reads and writes of `σ`: each `update(x)` of `Tₜ` becomes `read(x)` followed by `write(x)` of `Tₜ`; locks and unlocks are dropped. A position beyond the end of a list reads as the default entry `(0, 0)`.
