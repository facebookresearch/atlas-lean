# Transaction is well-formed in UNSAFE LOCKING POLICY

In UNSAFE LOCKING POLICY, a transaction is well-formed: every step is a lock, update or unlock; for each variable `x` it occurring in, it has at most one `lock(x)` and as many `unlock(x)`'s as `lock(x)`'s, the `lock(x)` before the `unlock(x)`; and every `update(x)` lies strictly between them.
