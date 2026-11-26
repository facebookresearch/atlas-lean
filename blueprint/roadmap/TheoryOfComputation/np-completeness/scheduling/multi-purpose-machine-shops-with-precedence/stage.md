# Stages of a multi-purpose machine shop with precedence

An instance of the multi-purpose machine shops with precedence is a tuple $(m, M, J, R, K)$ of a number $m$ of machines, a list $M = [\mu_1, \dots, \mu_r]$ of stage machine sets, a list $J$ of jobs, each an arbitrary list of natural numbers (its processing times, one per stage in a well-formed instance), a list $R$ of precedence pairs, and a bound $K$. Its stages are the positions $0, \dots, r-1$ of the list $M$, where $r$ is the length of $M$, one for each machine set.
