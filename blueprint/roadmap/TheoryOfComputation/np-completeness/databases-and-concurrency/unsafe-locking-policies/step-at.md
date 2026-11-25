# Step at position `r` of the schedule `σ` in UNSAFE LOCKING POLICY for two distributed transactions

For an instance `i` of UNSAFE LOCKING POLICY for two distributed transactions, the step at position `r` of the schedule `σ`, given by `(txn i (σ.getD r (0, 0)).1).1.getD (σ.getD r (0, 0)).2 (0, 0)`. A position beyond the end of a list reads as the default entry `(0, 0)`.
