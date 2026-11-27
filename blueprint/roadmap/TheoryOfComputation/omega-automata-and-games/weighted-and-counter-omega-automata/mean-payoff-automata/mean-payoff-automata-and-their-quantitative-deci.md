# Mean-payoff automata and their quantitative decision problems

A mean-payoff automaton is a finite automaton on infinite words with rational weights on its transitions; it assigns to each
word the best limit-average weight of its runs, and its quantitative decision problems compare these values with thresholds or
with another automaton.

A *quantitative language* over a finite alphabet $\Sigma$ is a function $L : \Sigma^\omega \to \mathbb{R}$. A *weighted
automaton* $A = \langle Q, q_I, \Sigma, \delta, \gamma \rangle$ has a finite set $Q$ of states, an initial state $q_I$, a total
transition relation $\delta \subseteq Q \times \Sigma \times Q$ (every state has at least one successor on every letter) and a
weight function $\gamma : \delta \to \mathbb{Q}$, with rationals written as pairs of binary integers. It is *deterministic* if
each state has a single successor on each letter. A *run* over $w = \sigma_1 \sigma_2 \cdots \in \Sigma^\omega$ is a sequence
$q_0 \sigma_1 q_1 \sigma_2 \cdots$ with $q_0 = q_I$ and $(q_i, \sigma_{i+1}, q_{i+1}) \in \delta$, and its weight sequence is
$v_0 v_1 \cdots$ with $v_i = \gamma(q_i, \sigma_{i+1}, q_{i+1})$. The *mean-payoff value* of a sequence $\bar{v}$ is one of

$$
\mathrm{LimInfAvg}(\bar{v}) = \liminf_{n \to \infty} \frac{1}{n} \sum_{i=0}^{n-1} v_i , \qquad
\mathrm{LimSupAvg}(\bar{v}) = \limsup_{n \to \infty} \frac{1}{n} \sum_{i=0}^{n-1} v_i .
$$

For $\mathrm{Val} \in \{\mathrm{LimInfAvg}, \mathrm{LimSupAvg}\}$ the *mean-payoff automaton* $A$ defines
$L_A(w) = \sup \{ \mathrm{Val}(\gamma(r)) : r \text{ a run of } A \text{ over } w \}$. Alternating mean-payoff automata extend
this with universal choices.

For quantitative languages $L, L_1, L_2$ given by automata and a rational threshold $\nu$:

- *quantitative emptiness*: is there $w \in \Sigma^\omega$ with $L(w) \ge \nu$?
- *quantitative universality*: is $L(w) \ge \nu$ for every $w \in \Sigma^\omega$?
- *quantitative language inclusion*: is $L_1(w) \le L_2(w)$ for every $w$?
- *quantitative language equivalence*: is $L_1(w) = L_2(w)$ for every $w$?

Universality is the special case of inclusion in which $L_1$ is constant. For deterministic mean-payoff automata all four
problems are decidable, and quantitative emptiness is decidable for nondeterministic ones.

## Depends on

None.

## Proof depends on

None.

## Sources

- K. Chatterjee, L. Doyen, H. Edelsbrunner, T. A. Henzinger and P. Rannou, "Mean-payoff automaton expressions", in *CONCUR 2010 – Concurrency Theory*, Lecture Notes in Computer Science 6269, pp. 269–283, Springer, 2010, doi:10.1007/978-3-642-15375-4_19; Section 2 of the version arXiv:1006.1492v1 (quantitative languages, weighted automata, runs, mean-payoff values, the decision problems) and the table of decidability results in Section 1.
