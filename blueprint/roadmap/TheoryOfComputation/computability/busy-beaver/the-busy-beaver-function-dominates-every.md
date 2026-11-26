# The busy beaver function dominates every computable function

Use Radó's Turing machines: a machine with $n$ states has one two-way infinite tape over the symbols $\{0, 1\}$, and for each state and
scanned symbol a transition that writes a symbol, moves the head one square left or right, and either enters a state or halts. Let
$S(n)$, the [shift function](busy-beaver-steps.md), be the largest number of steps taken by an $n$-state machine that halts when started
in its initial state on the all-$0$ tape, and $\Sigma(n) \le S(n)$, the [score function](busy-beaver-ones.md), the largest number of $1$s such a
machine leaves on its tape when it halts.

**Theorem.** For every computable $f : \mathbb{N} \to \mathbb{N}$ there is $n_f$ such that $S(n) > f(n)$ for all $n \ge n_f$. In particular $S$ is not
computable.

Proof: let $M_f$, with $c$ states, compute $f$. For each $n$ there is a machine $M_{f,n}$ with $c + O(\log n)$ states that writes $n$ on the blank
tape, simulates $M_f$ to compute $f(n)$, and then loops for $f(n)^2$ steps before halting, so $S(c + O(\log n)) > f(n)$ for all $n$. Since $S$ is nondecreasing (an extra unused state changes nothing) and $c + O(\log n) \le n$ for all large $n$, it follows that $S(n) > f(n)$ for all large $n$. Replacing the
final loop by a phase that writes $f(n) + 1$ further $1$s on fresh squares gives the same conclusion for $\Sigma$: for every computable $f$,
$\Sigma(n) > f(n)$ for all sufficiently large $n$, so $\Sigma$ is not computable either.

## Depends on

- [Busy Beaver shift function](busy-beaver-steps.md)
- [Busy Beaver score function](busy-beaver-ones.md)

## Sources

- S. Aaronson, "The Busy Beaver frontier", *ACM SIGACT News* 51(3):32–54, 2020, <https://www.scottaaronson.com/papers/bb.pdf>: Section 1 (the machine model, Figure 1, the definition of $BB(n)$, which is Radó's $S(n)$, and of $\Sigma(n) \le S(n)$) and Proposition 2 with its proof. The statement for $\Sigma$ is derived on this page by the same construction.
