# Inductive saturation characterizes well-nested reachability

For every MPDA (finitely many locations, transitions and stacks, finite alphabets), let $\mathrm{WR}$ be the least relation on control states containing all identity pairs and closed under: (i) $(s,s'')$ whenever $s\xrightarrow{\mathrm{nop}}s'$ and $(s',s'')\in\mathrm{WR}$; (ii) $(s,s''')$ whenever $s\xrightarrow{\mathrm{push}_k(\gamma)}s'$, $(s',s'')\in\mathrm{WR}$, $s''\xrightarrow{\mathrm{pop}_k(\gamma)}s'''$; (iii) composition. Then $(s,s')\in\mathrm{WR}$ iff some well-nested sequence of transitions labels a run of the control from $s$ to $s'$. $\mathrm{WR}$ is computed by saturation: close the set of pairs under these rules until a fixpoint is reached.

## Proof sketch

Induction on the generation of well-nested sequences in one direction and on the derivation of $\mathrm{WR}$ in the other; the saturation terminates since there are finitely many pairs.

Derived here (not stated in the cited source): each saturation round adds at least one of the at most $|S|^2$ pairs and costs time polynomial in $|S|$ and $|\Delta|$, so $\mathrm{WR}$ is computable in time polynomial in the size of the MPDA.

## Depends on

- [Multistack pushdown automata](multistack-pushdown-automata.md)
- [Well-nested sequences and matching of push/pop transitions](well-nested-transition-sequences.md)

## Sources

- S. Akshay, Paul Gastin, S. Krishna and Sparsa Roychowdhury, "Revisiting Underapproximate Reachability for Multipushdown Systems", Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2020), Lecture Notes in Computer Science 12078, 2020, Section 3, Lemma 1 and the two closure steps before it; arXiv:2002.05950.
