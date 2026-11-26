# Three-machine flow-shop schedule verifier

Given an encoded instance and start times,
the verifier checks each job's precedence and deadline and tests each pair for nonoverlap
on all three machines. Malformed inputs or certificates are rejected.

## Sources

- The row lengths and start-time inequalities in `WellFormed` and `FlowShopFeasible`.
