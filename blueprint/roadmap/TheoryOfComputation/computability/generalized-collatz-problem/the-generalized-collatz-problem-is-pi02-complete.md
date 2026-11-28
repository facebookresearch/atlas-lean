# The generalized Collatz problem is Π⁰₂-complete

Deciding, for a given Collatz function, whether the orbit of every positive integer reaches 1 is complete for the class $\Pi^0_2$ of the arithmetical hierarchy, so it is undecidable and strictly harder than the halting problem.

**Theorem (Kurtz and Simon).** The [generalized Collatz problem](collatz-functions.md), which asks, given a Collatz function $f$, whether for every integer $x > 0$ there is $i \in \mathbb{N}$ with $f^i(x) = 1$, is [$\Pi^0_2$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)-complete.

The problem lies in $\Pi^0_2$ because its defining condition has the form $\forall x\, \exists i$ with a decidable matrix. The classical $3x + 1$ problem is a single instance, whose answer is unknown.

## Proof sketch

Endrullis, Grabmayer and Hendriks obtain the hardness half as an immediate consequence of the $\Pi^0_2$-hardness of uniform halting of Fractran programs. From a [Fractran program](fractran-programs.md) $P = q_1, \dots, q_k$ form the Collatz function $f'_P$ that agrees with $f_P$ where $f_P$ is defined and takes the value $1$ where $f_P$ is undefined; its period is the least common multiple of the denominators of the $q_i$. A program with an integer fraction $q_i$ never halts. For every other program, $P$ halts on every $x > 0$ if and only if every orbit of $f'_P$ reaches $1$. This many-one reduction transfers $\Pi^0_2$-hardness from Fractran programs, a strict subclass of Collatz functions, to the generalized Collatz problem.

## Depends on

- [Collatz functions](collatz-functions.md)
- [The arithmetical class $\Pi_n$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Decidability by multi-stack machines](../decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Uniform halting of Fractran programs is Π⁰₂-complete](uniform-halting-of-fractran-programs-is-pi02.md)

## Sources

- S. A. Kurtz and J. Simon, "The undecidability of the generalized Collatz problem", in *Theory and Applications of Models of Computation (TAMC 2007)*, Lecture Notes in Computer Science 4484, Springer, 2007, pp. 542–553, doi:10.1007/978-3-540-72504-6_49: the original proof of $\Pi^0_2$-completeness, cited beside the sources read below.
- J. Endrullis, C. Grabmayer and D. Hendriks, "Complexity of Fractran and productivity", in *Automated Deduction – CADE-22*, Lecture Notes in Computer Science 5663, Springer, 2009, pp. 371–387, doi:10.1007/978-3-642-02959-2_28; read as arXiv:0903.4366v3, <https://arxiv.org/abs/0903.4366v3>: the paragraph after Theorem 2.2, which states the $\Pi^0_2$-completeness of the generalized Collatz problem with credit to the paper above and derives its hardness from Theorem 2.2, in the numbering of that version.
- B. Poonen, "Undecidable problems: a sampler", in J. Kennedy (ed.), *Interpreting Gödel: Critical Essays*, Cambridge University Press, 2014, pp. 211–241; read as arXiv:1204.0299v2, <https://arxiv.org/abs/1204.0299v2>: Section 10.2 (the generalized Collatz problem is undecidable) and the closing paragraph of the survey (it is strictly harder than the halting problem).
