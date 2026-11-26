# Well-formed instances of TWO-PROCESSOR TREE-PRECEDENCE SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME

An instance $(m, J, K, P)$ of TWO-PROCESSOR TREE-PRECEDENCE SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME is well-formed when

- $m > 0$, every task has positive length and positive weight, and $K > 0$;
- $m = 2$;
- all tasks have the same weight;
- every pair $(t, t') \in P$ names two tasks, that is, both indices are less than the number of tasks;
- the precedence relation $<$ given by $P$ is a strict partial order (irreflexive and transitive);
- the precedence relation is an in-tree (no task has more than one immediate successor) or an out-tree (no task has more than one immediate predecessor).
