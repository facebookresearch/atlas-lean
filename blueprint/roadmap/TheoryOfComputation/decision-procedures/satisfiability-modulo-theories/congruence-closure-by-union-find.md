# Congruence closure by union-find

Let $E$ be a finite set of equations between ground terms and $S$ the finite set of subterms of terms occurring in $E$. The congruence-closure algorithm, which starts from singleton classes on $S$, merges the classes of $s$ and $t$ for each equation $s = t$ of $E$, and repeatedly merges the classes of $f(s_1, \dots, s_n)$ and $f(t_1, \dots, t_n)$ in $S$ whenever each $s_i$ and $t_i$ lie in the same class, terminates and computes the least congruence relation on $S$ containing $E$: for $s, t \in S$, $s$ and $t$ end in the same class if and only if $E \models s = t$.

## Sources

- G. Nelson and D. C. Oppen, "Fast decision procedures based on congruence closure", *Journal of the ACM* 27(2):356–364, 1980
- R. Nieuwenhuis and A. Oliveras, "Fast congruence closure and extensions", *Information and Computation* 205(4):557–580, 2007, Section 2 and Theorem 9, <https://www.cs.upc.edu/~oliveras/IC.pdf>
- M. Fredrikson, "Deciding uninterpreted functions (and arrays)", lecture notes for 15-414, Carnegie Mellon University, 2023, Section 4.1, <https://www.cs.cmu.edu/~15414/s23/lectures/19-euf.pdf>
- D. Kroening and O. Strichman, *Decision Procedures: An Algorithmic Point of View*, 2nd ed., Springer, 2016
