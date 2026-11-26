# Is Tree Precedence

For the precedence relation of the listed arcs on $n$ jobs: every job has at most one [immediate successor](immediate-predecessor.md) (the intree condition), or every job has at most one immediate predecessor (the outtree condition). On its own this is not a tree test: a one-job self-loop passes, since the job is then its own intermediate and has no immediate predecessor or successor, and so do two isolated jobs. Acyclicity is checked separately by well-formedness, and connectivity is not required.
