# The faster-than relation of Markov processes is undecidable

No algorithm decides, for a finite labeled Markov process (given with rational transition probabilities) and two of its states, whether the first is faster than the second: whether every output word is at least as likely from the first state. The same holds for semi-Markov processes with any class of timing distributions.

**Processes.** A *semi-Markov process* $\mathcal{M} = (S, A, \Delta, \rho)$ has a finite set $S$ of states, a finite set $A$ of output labels, a transition function $\Delta$ assigning to each state $s$ a probability distribution $\Delta(s)$ on $S \times A$, and a residence-time function $\rho$ assigning to each state a [probability measure](../../../../../Probability/foundations/probability-measures/is-probability-measure.md) $\rho(s)$ on $\mathbb{R}_{\ge 0}$, its timing distribution, identified with its cumulative distribution function. In state $s$ the process fires a transition within time $t$ with probability $\rho(s)(t)$, moving to $s'$ while outputting $a$ with probability $\Delta(s)(s', a)$. For a word $w \in A^*$ the timing distribution $P_{\mathcal{M}}(s, w)$, the probability that the output from $s$ starts with $w$ within a given total time, is defined by $P_{\mathcal{M}}(s, \varepsilon) = 1$ and

$$
P_{\mathcal{M}}(s, aw) = \sum_{s' \in S} \Delta(s)(s', a) \cdot \bigl(\rho(s) * P_{\mathcal{M}}(s', w)\bigr),
$$

where $*$ is the convolution of timing distributions (the [convolution of probability measures](../../../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/conv.md)); write $P_{\mathcal{M}}(s, w, t)$ for its value at $t$. A *Markov process* $(S, A, \Delta)$ is the same without timing: $P_{\mathcal{M}}(s, \varepsilon) = 1$ and $P_{\mathcal{M}}(s, aw) = \sum_{s'} \Delta(s)(s', a) P_{\mathcal{M}}(s', w)$.

**The faster-than problem.** A state $s$ is *faster than* a state $s'$, written $s \preceq s'$, if $P_{\mathcal{M}}(s, w, t) \ge P_{\mathcal{M}}(s', w, t)$ for every word $w$ and every time $t$; for a Markov process, if $P_{\mathcal{M}}(s, w) \ge P_{\mathcal{M}}(s', w)$ for every word $w$. The *faster-than problem* asks, given a process and two states $s, s'$, whether $s \preceq s'$.

**Theorem (Pedersen, Fijalkow, Bacci, Larsen and Mardare).**

1. The faster-than problem is undecidable for Markov processes.
2. For semi-Markov processes, with any class of timing distributions, the faster-than problem is undecidable.

The source also shows that the problem cannot be approximated up to a multiplicative factor and that with a single output label it is as hard as the Positivity problem for linear recurrence sequences, whose decidability is open.

## Depends on

- [Probabilistic automata and cut-point languages](../probabilistic-automata-and-cut-point-languages.md)
- [Probability measure](../../../../../Probability/foundations/probability-measures/is-probability-measure.md)
- [Convolution of probability measures](../../../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/conv.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../emptiness-problem-for-probabilistic-automata.md)

## Expansion

From a probabilistic automaton $\mathcal{A}$ with states $Q$, initial state $q_0$ and accepting set $F$, build the Markov process with states $Q \times \{\ell, r\} \cup \{\top\}$ in which both copies follow the transitions of $\mathcal{A}$ with probability scaled by $1/(2|A|)$, a state $(p, \ell)$ with $p \in F$ moves to $\top$ with probability $1/(2|A|)$ on each letter, and every state $(p, r)$ moves to $\top$ with probability $1/(4|A|)$. Then $P(s, wa) = (2|A|)^{-(|w|+1)}(1 + P_{\mathcal{A}}(w))$ and $P(s', wa) = (2|A|)^{-(|w|+1)} \cdot \tfrac{3}{2}$ for $s = (q_0, \ell)$ and $s' = (q_0, r)$, so $s \preceq s'$ exactly when $P_{\mathcal{A}}(w) \ge 1/2$ for all nonempty $w$. This universality question is the complement of the emptiness of the cut-point language at $1/2$ for the automaton with complemented accepting set, which is undecidable. For semi-Markov processes, constant residence-time functions (or Dirac measures at $0$) reduce the timed relation to the untimed one.

## Sources

- M. R. Pedersen, N. Fijalkow, G. Bacci, K. G. Larsen and R. Mardare, "Timed comparisons of semi-Markov processes", in *Language and Automata Theory and Applications (LATA 2018)*, Lecture Notes in Computer Science, Springer, 2018, pp. 271–283, doi:10.1007/978-3-319-77313-1_21; read in arXiv:1711.10216v3: the definitions of semi-Markov processes, their probabilities and the faster-than relation, the undecidability theorem for Markov processes with the derived-process construction, and the corollary for semi-Markov processes in the section on hardness results.
