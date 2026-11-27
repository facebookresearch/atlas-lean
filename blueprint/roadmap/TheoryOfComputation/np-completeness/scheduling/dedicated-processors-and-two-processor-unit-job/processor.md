# Processor of a task in precedence scheduling with dedicated processors

An instance of precedence scheduling with dedicated processors is a pair of a PRECEDENCE CONSTRAINED SCHEDULING instance, whose tasks are the positions $0, \dots, n-1$ of its list of task lengths, and a list $q$ of natural numbers. The processor $p(t)$ of task $t$ is the entry of $q$ at position $t$, and $0$ when $q$ has no entry at that position. That $q$ has exactly one entry per task, each below the number of processors, is a condition of a well-formed instance, not of this definition.
