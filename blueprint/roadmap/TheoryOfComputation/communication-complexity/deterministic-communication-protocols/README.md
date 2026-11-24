# Deterministic communication protocols

In Yao's model (A. C. Yao, STOC 1979) Alice holds $x \in X$, Bob holds $y \in Y$, and they
exchange bits to compute $f(x, y) \in \{0, 1\}$. A deterministic protocol is a binary tree whose
internal nodes are owned by one party and whose leaves carry the output; its cost is the depth of
the tree, and the deterministic communication complexity $D(f)$ is the least cost of a protocol
computing $f$. Everything below rests on two facts about protocol trees: a tree of depth $d$ has
at most $2^d$ leaves, and the inputs reaching a leaf form a combinatorial rectangle $A \times B$
on which $f$ is constant. Counting leaves against a fooling set, or against the rank of the
communication matrix (each 1-leaf contributes a rank-one matrix), gives the lower bounds
$D(f) \ge \log_2 |S|$ and $D(f) \ge \log_2 \operatorname{rank} M_f$; for the equality function
on $n \ge 1$ bits they show that the trivial protocol, with $n + 1$ bits, is optimal. Whether the
rank bound is polynomially tight is the open log-rank conjecture. The presentation follows A. Rao and A. Yehudayoff, *Communication Complexity* (early
draft), Chapters 1 and 2.

- [Deterministic two-party protocol](protocol.md)
- [Output of a protocol](eval.md)
- [Communication cost of a protocol](depth.md)
- [A protocol computes a function](computes.md)
- [Transcript of a protocol](transcript.md)
- [Leaves of a protocol tree](leaves.md)
- [A protocol of depth $d$ has at most $2^d$ leaves](card-leaves-le.md)
- [Transcripts are leaf paths](transcript-mem-leaves.md)
- [The output is determined by the transcript](eval-eq-of-transcript-eq.md)
- [Crossing property of transcripts](transcript-cross.md)
- [Rectangle lemma](transcript-eq-iff.md)
- [Leaf rectangles are monochromatic](eq-of-transcript-eq.md)
- [Fooling set](is-fooling-set.md)
- [Fooling-set pairs reach distinct leaves](inj-on-transcript-of-is-fooling-set.md)
- [Fooling-set lower bound](card-le-two-pow-of-is-fooling-set.md)
- [Communication matrix](comm-matrix.md)
- [Rank lower bound](rank-le-two-pow-depth.md)
- [Alice reveals her input from a list](alice-reveal.md)
- [Bob reveals his input from a list](bob-reveal.md)
- [Alice reveals her input](eval-alice-reveal.md)
- [Bob reveals his input](eval-bob-reveal.md)
- [Every function on finite inputs has a protocol](exists-computes.md)
- [Alice sends a $b$-bit message](alice-sends.md)
- [Output after Alice sends a message](eval-alice-sends.md)
- [Cost of sending a $b$-bit message](depth-alice-sends-le.md)
- [Deterministic communication complexity](comm-complexity.md)
- [An optimal protocol exists](exists-depth-eq-comm-complexity.md)
- [Every protocol costs at least the communication complexity](comm-complexity-le-depth.md)
- [Fooling-set lower bound for the communication complexity](card-le-two-pow-comm-complexity.md)
- [Rank lower bound for the communication complexity](rank-le-two-pow-comm-complexity.md)
- [Log-rank lower bound](log-rank-le-comm-complexity.md)
- [Equality function](eq-fn.md)
- [The trivial protocol for equality](eq-protocol.md)
- [The trivial protocol computes equality](eq-protocol-computes.md)
- [Upper bound for equality](depth-eq-protocol-le.md)
- [Lower bound for equality](lt-depth-of-computes-eq-fn.md)
- [Deterministic communication complexity of equality](comm-complexity-eq-fn.md)
- [Equality of empty strings](comm-complexity-eq-fn-zero.md)
- [The log-rank conjecture (open)](log-rank-conjecture.md)

## Related topics

- [Randomized communication protocols](../randomized-communication-protocols/README.md): with shared random bits equality costs a constant number of bits, against $n + 1$ deterministically.
