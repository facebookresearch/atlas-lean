# Whether a finite-valued transducer has an equivalent deterministic two-tape automaton is undecidable

No algorithm decides whether the relation of a finite-valued nondeterministic finite transducer, even an unambiguous one, is accepted by a
deterministic two-tape automaton; this extends Fischer and Rosenberg's undecidability result for general two-tape automata.

A *nondeterministic finite transducer* (NFT) $T = (Q, \Sigma, \Gamma, \delta, q_0, F)$ reads one input letter per step and writes a finite output word, $\delta$ mapping $Q \times \Sigma$ to finite
subsets of $Q \times \Gamma^*$; it accepts the relation $L(T) \subseteq \Sigma^* \times \Gamma^*$ of input-output pairs of its accepting runs. It is *finite-valued* if some $k$ bounds the number of outputs of
each input, *functional* if $k = 1$ works, and *unambiguous* if each input has at most one accepting run. A *two-tape deterministic finite automaton* reads an
input word and an output word, each followed by an end marker, with one head per tape moving left to right: in each step its transition function maps the state and the two scanned
symbols to a new state and, for each head, the choice to stay or advance, with at least one head advancing and no head moving past its end marker; it accepts the pairs on which it ends
in an accepting state. Two-tape nondeterministic automata accept exactly the relations of NFTs, up to empty inputs.

**Theorem.** It is undecidable, given a finite-valued NFT $T$, whether there is a deterministic two-tape automaton $A$ with $L(A) = L(T)$. The problem remains undecidable for functional
NFTs and for unambiguous NFTs.

Consequently, finite-valued, functional and unambiguous NFTs are strictly more expressive than deterministic two-tape automata accepting relations of the same kind. Fischer and
Rosenberg had shown the undecidability for general two-tape automata, through relations that are not finite-valued. By contrast, whether an NFT has an equivalent deterministic transducer is decidable: Choffrut characterized such NFTs by the twinning property, which is decidable in polynomial time.

## Depends on

- [Rational relations and transducers](rational-relations-and-transducers.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The proof characterizes the finite-valued NFTs with an equivalent deterministic two-tape automaton as those with *bounded trailing*, a quantitative property of how far the output of
one accepting run can lag behind or run ahead of another on the same input, refining Choffrut's bounded variation. It then reduces the problem whether a Turing machine started on the empty tape
reaches configurations of arbitrary length, which is undecidable, to bounded trailing: from the machine it builds an unambiguous NFT that has bounded trailing exactly when the machine's
configurations stay bounded in length.

## Sources

- E. Burjons, F. Frei and M. Raszyk, "From finite-valued nondeterministic transducers to deterministic two-tape automata", in *36th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2021)*, IEEE, 2021, pp. 1–13, doi:10.1109/LICS52264.2021.9470688; read in arXiv:2005.13710v3: the undecidability theorem of the section "Bounded Trailing is Undecidable" with its corollary on Turing machines, the theorems that bounded trailing is sufficient and necessary, the definition of deterministic two-tape automata in the Preliminaries, and the introduction.
