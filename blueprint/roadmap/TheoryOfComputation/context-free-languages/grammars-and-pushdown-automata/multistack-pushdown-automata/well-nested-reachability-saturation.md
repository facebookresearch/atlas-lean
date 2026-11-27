# Inductive saturation characterizes well-nested reachability

For every MPDA (arbitrary state and alphabet types, finitely many stacks), let $\mathrm{WR}$ be the least relation on control states containing all identity pairs and closed under: (i) $(s,s'')$ whenever $s\xrightarrow{\mathrm{nop}}s'$ and $(s',s'')\in\mathrm{WR}$; (ii) $(s,s''')$ whenever $s\xrightarrow{\mathrm{push}_k(\gamma)}s'$, $(s',s'')\in\mathrm{WR}$, $s''\xrightarrow{\mathrm{pop}_k(\gamma)}s'''$; (iii) composition. Then $(s,s')\in\mathrm{WR}$ iff some well-nested sequence of transitions labels a run of the control from $s$ to $s'$. When the states and the transitions are given as finite tables, $\mathrm{WR}$ is computable by saturation in time polynomial in the size of these tables.

## Proof sketch

Induction on the generation of well-nested sequences in one direction and on the derivation of $\mathrm{WR}$ in the other; the saturation terminates since there are finitely many pairs.

## Depends on

- [Well-nested sequences and matching of push/pop transitions](well-nested-transition-sequences.md)

## Sources

- S. Akshay, Paul Gastin, S. Krishna and Sparsa Roychowdhury, "Revisiting Underapproximate Reachability for Multipushdown Systems", Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2020), arXiv:2002.05950, 2020, Lemma 1.
