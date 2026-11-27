# Yao and Beigel–Tarui: ACC0 circuits are quasi-polynomial SYM ∘ AND circuits

For every depth $d$ and modulus $m\ge2$ there is a constant $f(d,m)$ (estimated by Williams to be at most $m^{O(d)}$) such that every circuit of size $s\ge n$ and depth $d$ on $n$ inputs with $\neg$, unbounded fan-in $\wedge,\vee$ and $\mathrm{MOD}_m$ gates computes the same function as a $\mathrm{SYM}\circ\mathrm{AND}$ circuit with $s^{O(\log^{f(d,m)}s)}$ AND gates, each of fan-in $O(\log^{f(d,m)}s)$ and reading only positive literals. The equivalent circuit can be constructed in time $s^{O(\log^{f(d,m)}s)}$, and the symmetric output function, given the number of satisfied AND gates, can be evaluated in the same time. Hence every language in $\mathsf{ACC}^0$ has $\mathrm{SYM}\circ\mathrm{AND}$ circuits of polylogarithmic fan-in and quasi-polynomial size.

## Proof sketch

Replace each composite-modulus gate by AND gates of prime-modulus gates, and replace AND/OR gates by probabilistic constant-depth circuits of prime-modulus gates and polylogarithmic fan-in AND gates sharing $\mathrm{poly}(\log s)$ random bits (the Valiant–Vazirani trick behind the Razborov–Smolensky approximation). Enumerate all random seeds below a majority gate, push the small AND gates to the bottom, and collapse the layers of modular gates with modulus-amplifying polynomials (Toda, Yao, Beigel–Tarui) into one symmetric function of a sum of AND gates.

## Depends on

- [SYM ∘ AND circuits](sym-and-circuits.md)
- [The class $\mathsf{ACC}^0$](../../../complexity-classes/time-and-space-complexity-classes/acc0.md)

## Proof depends on

- [Razborov–Smolensky polynomial approximation of AC0[p]](../razborovsmolensky-polynomial-approximation-of.md)

## Sources

- Andrew Chi-Chih Yao, "On ACC and Threshold Circuits", Proceedings of the 31st Annual Symposium on Foundations of Computer Science (FOCS 1990), 1990.
- Richard Beigel, Jun Tarui, "On ACC", Computational Complexity 4, 1994.
- Eric Allender, Vivek Gore, "A Uniform Circuit Lower Bound for the Permanent", SIAM Journal on Computing 23(5), 1994 (constructive version).
- Ryan Williams, "Nonuniform ACC Circuit Lower Bounds", Journal of the ACM 61(1), Article 2, 2014 (Lemma 4.1 and Appendices A–B).
