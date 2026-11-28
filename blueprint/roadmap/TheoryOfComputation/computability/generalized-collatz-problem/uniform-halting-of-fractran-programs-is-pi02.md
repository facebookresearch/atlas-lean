# Uniform halting of Fractran programs is Π⁰₂-complete

Deciding whether a Fractran program halts on every positive starting value is complete for the class $\Pi^0_2$ of the arithmetical hierarchy.

**Theorem (Endrullis, Grabmayer and Hendriks).** The uniform halting problem for [Fractran programs](fractran-programs.md), which asks, given a program $P$, whether $P$ halts on every starting value $n_0 \in \mathbb{N}$ with $n_0 > 0$, is [$\Pi^0_2$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)-complete.

Membership in $\Pi^0_2$ is immediate from the form $\forall n_0\, \exists i$ of the condition. The program is the input; there is no bound on its length or on its fractions.

## Depends on

- [Fractran programs](fractran-programs.md)
- [The arithmetical class $\Pi_n$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)

## Proof depends on

None.

## Expansion

Hardness is shown by reduction from the uniform halting problem for Turing machines, halting from every initial or intermediate configuration, which is $\Pi^0_2$-complete by a result of Herman that the source recalls (Theorem 2.4 there). A Turing machine is translated into a Fractran program in which pairwise distinct primes record the state, the symbol under the head and the two halves of the tape in their exponents, and a fixed finite sequence of Fractran steps simulates one machine step. The difficulty the source deals with is that the program must halt on every positive integer, including those that do not encode a configuration in the intended form, exactly when the machine halts from every configuration.

## Sources

- J. Endrullis, C. Grabmayer and D. Hendriks, "Complexity of Fractran and productivity", in *Automated Deduction – CADE-22*, Lecture Notes in Computer Science 5663, Springer, 2009, pp. 371–387, doi:10.1007/978-3-642-02959-2_28; read as arXiv:0903.4366v3, <https://arxiv.org/abs/0903.4366v3>: Theorem 2.2 (uniform halting of Fractran programs is $\Pi^0_2$-complete), Theorem 2.4 (uniform halting of Turing machines) and the translation of Turing machines into Fractran programs in Section 2, in the numbering of that version.
