# Timed words and timed languages

A *time sequence* is an infinite sequence $\tau = \tau_1 \tau_2 \cdots$ of positive real numbers that is strictly increasing
($\tau_i < \tau_{i+1}$ for all $i \ge 1$) and unbounded: for every $t \in \mathbb{R}$ there is an $i \ge 1$ with $\tau_i > t$.
A *timed word* over a finite alphabet $\Sigma$ is a pair $(\sigma, \tau)$ of an infinite word $\sigma = \sigma_1 \sigma_2 \cdots \in \Sigma^\omega$
and a time sequence $\tau$; it presents the letter $\sigma_i$ at time $\tau_i$. A *timed language* over $\Sigma$ is a set of timed
words over $\Sigma$.

For a timed language $L$, $\mathrm{Untime}(L)$ is the $\omega$-language of the words $\sigma \in \Sigma^\omega$ such that
$(\sigma, \tau) \in L$ for some time sequence $\tau$.

A variant in which consecutive time stamps may coincide ($\tau_i \le \tau_{i+1}$) is also used; the results on timed
automata in this folder hold in it as well.

## Sources

- R. Alur and D. L. Dill, "A theory of timed automata", *Theoretical Computer Science* 126(2):183–235, 1994: Definition 3.1 (time sequences, timed words and timed languages), the remark after it on weakly monotone time sequences, and Definition 3.3 (Untime).
