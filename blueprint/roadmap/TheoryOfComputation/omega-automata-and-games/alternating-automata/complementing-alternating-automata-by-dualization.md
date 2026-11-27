# Complementing alternating automata by dualization

The *dual* $\bar\theta$ of a positive Boolean formula $\theta$ exchanges $\wedge$ with $\vee$ and $\mathrm{true}$ with $\mathrm{false}$. For an
[alternating automaton](alternating-automata-on-finite-words.md) $\mathcal{A} = (\Sigma, S, s_0, \rho, F)$, the automaton
$\bar{\mathcal{A}} = (\Sigma, S, s_0, \bar\rho, S \setminus F)$ with $\bar\rho(s, a) = \overline{\rho(s, a)}$ accepts exactly
$\Sigma^* \setminus L(\mathcal{A})$. Complementation of alternating automata is therefore linear in size.

## Depends on

- [Alternating automata on finite words](alternating-automata-on-finite-words.md)

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, Lecture Notes in Computer Science 1043, Springer, 1996, pp. 238–266; numbering from the author's posted version, <https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf>: Section 2.5, the definition of the dual operation and Proposition 17.
