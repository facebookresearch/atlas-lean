# Rational time stamps suffice for the untimed language of a timed automaton

Let $L$ be a [timed regular language](timed-buchi-automata.md) over $\Sigma$. A word $\sigma \in \Sigma^\omega$ belongs to
$\mathrm{Untime}(L)$ if and only if there is a time sequence $\tau$ with $\tau_i \in \mathbb{Q}$ for every $i \ge 1$ such that
$(\sigma, \tau) \in L$. Only the density of the time domain matters: restricting time stamps to rationals does not
change the untimed language of a timed automaton.

## Depends on

- [Timed Büchi automata and timed regular languages](timed-buchi-automata.md)
- [Timed words and timed languages](timed-words-and-timed-languages.md)

## Sources

- R. Alur and D. L. Dill, "A theory of timed automata", *Theoretical Computer Science* 126(2):183–235, 1994: Theorem 3.17 and its proof, which chooses rational stamps preserving the comparisons of all differences $\tau_i - \tau_j$ with the integral multiples of a common divisor of the constants.
