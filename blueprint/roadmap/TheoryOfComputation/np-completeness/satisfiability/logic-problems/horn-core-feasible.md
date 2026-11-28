# Feasible instances of HORN CORE

An instance $(n, M, K)$ is feasible when some sublist $M'$ of the list $M$ (entries kept in order, with their repetitions) has at least $K$ entries and [is the model set](is-horn-model-set.md) of a Horn formula on the $n$ variables. The count is of list entries, not distinct assignments: two copies of $[\mathrm{false}]$ meet $K = 2$ through the formula $\lnot x_0$, although it has only one model. Well-formed instances list each assignment once.
