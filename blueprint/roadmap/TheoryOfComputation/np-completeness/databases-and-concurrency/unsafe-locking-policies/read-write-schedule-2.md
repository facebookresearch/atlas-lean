# Schedule of reads and writes of `σ` in UNSAFE LOCKING POLICY

For an instance `i` of UNSAFE LOCKING POLICY, the schedule of reads and writes of `σ`: each `update(x)` of `Tₜ` becomes `read(x)` followed by `write(x)` of `Tₜ`; locks and unlocks are dropped.
