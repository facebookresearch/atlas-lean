# i-sequences and records

Let $\mathcal{G}$ be a [parity game](../parity-games/parity-game.md) with $n$ positions, whose priorities are positive integers, and consider a finite or infinite play
$v_1 v_2 \cdots$. An *$i$-sequence for Eve* in it is a sequence of $2^i$ positions $a_1, \dots, a_{2^i}$ visited in this order (at increasing times, not
necessarily consecutive) such that for every $k < 2^i$ the largest priority of the positions visited from the visit of $a_k$ to the visit of $a_{k+1}$, both
included, is even.

Let $\ell$ be the least integer with $2^\ell > 2n$. The *record* (winning statistics) of Eve is a tuple $(b_\ell, \dots, b_1, b_0)$ in which each $b_i$ is $0$ or a priority;
it starts with every entry $0$. The entry $0$ means that no sequence is tracked and has neither parity: below, "even" and "odd" apply only to positive entries. When the play moves to a position of priority $b$, the record changes only if $b$ is even or $b > b_i > 0$ for some $i$. In
that case let $i$ be the largest index such that

- (a) $b_i$ is $0$ or odd, while $b$ is even and every $b_j$ with $j < i$ is a positive even priority, or
- (b) $0 < b_i < b$,

and set $b_i := b$ and $b_j := 0$ for every $j < i$. Eve is *declared the winner* once $b_\ell \ne 0$. The record of Adam is the same construction with even
and odd exchanged.

These are the play summaries of Calude, Jain, Khoussainov, Li and Stephan. Rule (a) lets an incoming even priority replace an odd entry
when all lower entries are positive and even, even if it is smaller; on the losing play $1, 2, 1, 1, \dots$ through three positions, a single $2$ sets only $b_0$. The variant in the cited chapter, as run in its worked example, cannot: on the play $3, 2, 2, \dots$ through two positions of
priorities $3$ and $2$, which Eve wins, that variant keeps the odd $b_0 = 3$ forever, while the record above ignores the $3$ and then counts in binary: the first $2$ sets $b_0$, the second $b_1$, and the eighth $b_3 = b_\ell$.

## Depends on

- [Parity game](../parity-games/parity-game.md)

## Sources

- C. S. Calude, S. Jain, B. Khoussainov, W. Li and F. Stephan, "Deciding parity games in quasipolynomial time", *Proceedings of the 49th ACM STOC*, 2017 (numbering of the authors' preprint, <http://www.cmap.polytechnique.fr/~gaubert/COURSM2/PARITYGAMES/paritygame.pdf>): Section 2, the definition of $i$-sequences, the winning statistics, the update rules (a) and (b), the termination condition ($b_i \ne 0$ with $2^i > 2n$) and the worked example.
- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Section 2.4, "i-sequences" and "The update rule", the variant contrasted above.
