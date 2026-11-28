# The infinite PCP in a regular ω-language is Σ¹₁-complete

Deciding whether a Post correspondence instance has an infinite solution whose index sequence belongs to a given regular
ω-language is $\Sigma^1_1$-complete, so it is not even arithmetical.

An instance of the *infinite Post correspondence problem in a regular ω-language* ($\omega$-PCP(Reg)) consists of two
$n$-tuples $(x_1, \dots, x_n)$ and $(y_1, \dots, y_n)$ of nonempty words over a finite alphabet $\Gamma$ and a Büchi
automaton $\mathcal{A}$ over the alphabet $\{1, \dots, n\}$, accepting by the [Büchi condition](../../omega-automata-and-games/emptiness-of-b-chi-automata/mem-language-iff.md).
A *solution* is an infinite sequence $i_1 i_2 i_3 \cdots \in L(\mathcal{A})$ with

$$
x_{i_1} x_{i_2} x_{i_3} \cdots = y_{i_1} y_{i_2} y_{i_3} \cdots .
$$

Without the automaton (or with $L(\mathcal{A}) = \{1, \dots, n\}^\omega$) this is the
[infinite Post correspondence problem](the-infinite-post-correspondence-problem.md) restricted to nonerasing instances: since all $x_i, y_i$ are nonempty, the two infinite products are equal exactly when $x_{i_1} \cdots x_{i_k}$ and $y_{i_1} \cdots y_{i_k}$ are comparable for every $k$.

**Theorem.** The set of (codes of) instances of $\omega$-PCP(Reg) that have a solution is
[$\Sigma^1_1$-complete](../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md).

The plain infinite Post correspondence problem is undecidable (Ruohonen; Gire), and so is the finite one; restricting
solutions to a regular ω-language raises the complexity from the arithmetical hierarchy to $\Sigma^1_1$-completeness. The
source does not fix the size of $\Gamma$ in the instances produced by the reduction beyond what the Turing machine requires.

## Depends on

- [The infinite Post correspondence problem](the-infinite-post-correspondence-problem.md)
- [Büchi acceptance condition](../../omega-automata-and-games/emptiness-of-b-chi-automata/mem-language-iff.md)
- [Analytical hierarchy](../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

*Membership.* From an instance one computes a Büchi Turing machine accepting exactly the solutions; non-emptiness of the
ω-language of a Büchi Turing machine is $\Sigma^1_1$ (there exist an infinite word and an accepting run, an existential
function quantifier followed by an arithmetical matrix).

*Hardness.* Reduce Harel's $\Sigma^1_1$-complete problem: does a nondeterministic Turing machine started on the blank tape
have an infinite computation that re-enters its initial state $q_0$ infinitely often? The lists $x, y$ are the standard
dominoes simulating the machine's computation as a sequence of configurations separated by $\#$, starting with the pair
$(\#, \# q_0 \#)$. The Büchi automaton accepts the index sequences that begin with $1$ and use infinitely often an index whose
$y$-word contains $q_0$. A solution is then exactly an infinite computation visiting $q_0$ infinitely often.

## Sources

- O. Finkel, "Three applications to rational relations of the high undecidability of the infinite Post correspondence problem in a regular ω-language", *International Journal of Foundations of Computer Science* 23(7):1481–1497, 2012, doi:[10.1142/S0129054112400606](https://doi.org/10.1142/S0129054112400606). Numbering of the version read, arXiv:1107.5886v1: Theorem 3.3 (Σ¹₁-completeness), Theorem 3.2 (the infinite PCP), Definition 2.1 (Büchi automata) and Theorem 2.10 (Harel's Σ¹₁-complete problem).
