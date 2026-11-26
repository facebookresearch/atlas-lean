# Evaluation of an oracle machine with adaptive queries

Let $\alpha$ be a type of
oracle answers and $\beta$ a type of outputs, and call a list of pairs of a bitstring and an
element of $\alpha$ a history. Fix a length cap $c \in \mathbb{N}$, a next-query function $N$
sending an input bitstring and a history to a bitstring, a decision function $F$ sending an
input bitstring and a history to an element of $\beta$, an oracle $O$ from bitstrings to
$\alpha$ and an input bitstring $x$. For a number $f \in \mathbb{N}$ of remaining queries and a
history $h$, the evaluation $E_f(h)$ is defined by recursion on $f$: $E_0(h) = F(x, h)$, and for
$E_{f+1}(h)$ let $q = N(x, h)$; if $q$ has length at most $c$, then $E_{f+1}(h) = E_f(h')$,
where $h'$ is $h$ with the pair $(q, O(q))$ appended at the end, and otherwise
$E_{f+1}(h) = F(x, h)$.

Dummy queries simulate early halting, so a fixed number of queries is without loss of
generality. At use sites the cap is polynomial in the length of $x$, so polynomial running time
of $N$ and $F$ on each call gives polynomial total running time in the length of $x$.
