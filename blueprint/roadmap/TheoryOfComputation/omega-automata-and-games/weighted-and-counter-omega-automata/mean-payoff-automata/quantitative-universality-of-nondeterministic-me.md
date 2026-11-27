# Quantitative universality of nondeterministic mean-payoff automata is undecidable

No algorithm decides whether every infinite word has value at least a given threshold under a nondeterministic mean-payoff
automaton; quantitative inclusion and equivalence are undecidable for the same reason.

Let $A$, $A_1$, $A_2$ range over [mean-payoff automata](mean-payoff-automata-and-their-quantitative-deci.md), with
$\mathrm{LimInfAvg}$ or $\mathrm{LimSupAvg}$ values, and $\nu$ over rational thresholds.

**Theorem.** For nondeterministic mean-payoff automata the quantitative universality problem (is $L_A(w) \ge \nu$ for all
$w \in \Sigma^\omega$?), the quantitative language-inclusion problem (is $L_{A_1}(w) \le L_{A_2}(w)$ for all $w$?) and the
quantitative language-equivalence problem are undecidable. For alternating mean-payoff automata the quantitative emptiness,
universality, language-inclusion and language-equivalence problems are undecidable.

By contrast, quantitative emptiness is decidable for nondeterministic mean-payoff automata, all four problems are decidable
for deterministic ones, and the source shows that they are decidable, in 4EXPTIME, for mean-payoff automaton expressions, the
closure of deterministic mean-payoff automata under $\max$, $\min$, sum and complement.

## Depends on

- [Mean-payoff automata and their quantitative decision problems](mean-payoff-automata-and-their-quantitative-deci.md)

## Proof depends on

None.

## Expansion

Degorre, Doyen, Gentilini, Raskin and Toruńczyk proved, by a reduction from the halting problem of two-counter machines, that
in two-player mean-payoff games with a blind player $1$ it is undecidable whether player $1$ has a blind strategy $\sigma$ with
$\inf_\tau P(\sigma, \tau) > \nu$; the reduction is such that, for $\nu = 0$, the dual question whether
$\sup_\tau P(\sigma, \tau) \ge \nu$ for every blind $\sigma$ is undecidable too. Universality of a nondeterministic mean-payoff
automaton is such a game: player $1$ chooses the word, which is a blind strategy, and player $2$ resolves the nondeterminism.
Hence universality is undecidable, and inclusion and equivalence, which contain it as the case of a constant automaton, are
undecidable as well. Universality for nondeterministic automata reduces to emptiness and to universality for alternating
automata.

## Sources

- K. Chatterjee, L. Doyen, H. Edelsbrunner, T. A. Henzinger and P. Rannou, "Mean-payoff automaton expressions", in *CONCUR 2010 – Concurrency Theory*, Lecture Notes in Computer Science 6269, pp. 269–283, Springer, 2010, doi:10.1007/978-3-642-15375-4_19; Section 5 of the version arXiv:1006.1492v1: the undecidability theorem stated after the decidability theorem for expressions, with its proof sketch in the appendix.
