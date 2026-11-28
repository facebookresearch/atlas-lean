# Collatz functions

A Collatz function acts on natural numbers by an affine map chosen by the residue of the argument modulo a fixed period; the generalized Collatz problem asks whether every orbit of a given Collatz function reaches 1.

**Definition.** A *Collatz function* is a function $f \colon \mathbb{N} \to \mathbb{N}$ of the form

$$
f(n) = a_i n + b_i \qquad \text{if } n \equiv i \pmod{p}, \quad 0 \le i < p,
$$

for some $p \ge 1$ and rational numbers $a_0, \dots, a_{p-1}, b_0, \dots, b_{p-1}$ such that $f(n) \in \mathbb{N}$ for every $n \in \mathbb{N}$. It is given by $p$ and the rationals $a_i, b_i$. The *generalized Collatz problem* asks, given a Collatz function $f$, whether for every integer $x > 0$ there is $i \in \mathbb{N}$ with $f^i(x) = 1$.

The classical [Collatz map](../../../NumberTheory/integer-sequences/iterated-self-referential/collatz-problem/collatz-step.md), $x \mapsto x/2$ for even $x$ and $x \mapsto 3x + 1$ for odd $x$, is a Collatz function with $p = 2$.

## Depends on

- [The Collatz map](../../../NumberTheory/integer-sequences/iterated-self-referential/collatz-problem/collatz-step.md)

## Proof depends on

None.

## Sources

- J. Endrullis, C. Grabmayer and D. Hendriks, "Complexity of Fractran and productivity", in *Automated Deduction – CADE-22*, Lecture Notes in Computer Science 5663, Springer, 2009, pp. 371–387, doi:10.1007/978-3-642-02959-2_28; read as arXiv:0903.4366v3, <https://arxiv.org/abs/0903.4366v3>: the definition of Collatz functions and of the generalized Collatz problem in the paragraph after Theorem 2.2, in the numbering of that version.
- B. Poonen, "Undecidable problems: a sampler", in J. Kennedy (ed.), *Interpreting Gödel: Critical Essays*, Cambridge University Press, 2014, pp. 211–241; read as arXiv:1204.0299v2, <https://arxiv.org/abs/1204.0299v2>: the generalized Collatz problem in Section 10.2 of that version.
