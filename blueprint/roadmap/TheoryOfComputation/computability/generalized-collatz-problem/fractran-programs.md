# Fractran programs

A Fractran program is a finite list of positive fractions; it repeatedly multiplies the current natural number by the first fraction that gives an integer, and halts when no fraction does.

**Definition.** A *Fractran program* is a finite list $P = q_1, \dots, q_k$ of positive rational numbers. Its one-step function is the partial function $f_P \colon \mathbb{N} \rightharpoonup \mathbb{N}$ with $f_P(n) = n q_i$ for the least $i$ such that $n q_i \in \mathbb{N}$, and $f_P(n)$ undefined if there is no such $i$. The program *halts on* $n$ if $f_P^i(n)$ is undefined for some $i \in \mathbb{N}$. The *uniform halting problem* for Fractran programs asks, given $P$, whether $P$ halts on every starting value $n_0 \in \mathbb{N}$ with $n_0 > 0$.

The empty program halts at once on every input. A program containing an integer fraction never halts, since that fraction always applies.

## Depends on

None.

## Proof depends on

None.

## Sources

- J. Endrullis, C. Grabmayer and D. Hendriks, "Complexity of Fractran and productivity", in *Automated Deduction – CADE-22*, Lecture Notes in Computer Science 5663, Springer, 2009, pp. 371–387, doi:10.1007/978-3-642-02959-2_28; read as arXiv:0903.4366v3, <https://arxiv.org/abs/0903.4366v3>: Definition 2.1 (the step function of a Fractran program and halting) and Theorem 2.2 (the uniform halting problem), in the numbering of that version.
