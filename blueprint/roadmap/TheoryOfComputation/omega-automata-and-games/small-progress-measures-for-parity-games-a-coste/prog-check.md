# Prog Check

The progress-measure condition for the edge `v → w`: at even
priority of `v` the tuple must not increase in the truncated lexicographic
order at that priority, at odd priority it must strictly decrease. The
top element `none` at `v` satisfies every comparison (a losing position
imposes no progress requirement); a finite tuple at `v` never satisfies
the condition against `none` at `w`, since `none` is the top element.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", *Proceedings of STACS 2000*, LNCS 1770, 290-301.
