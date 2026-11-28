# Infinitary rational relations and ω-rational functions

An infinitary rational relation is a relation between infinite words accepted by a Büchi transducer; when it is the graph
of a partial function, that function is ω-rational, and its continuity set is the set of points where it is continuous.

**Büchi transducers.** A *Büchi transducer* is a tuple $\mathcal{T} = (K, \Sigma, \Gamma, \Delta, q_0, F)$ with a finite set
$K$ of states, finite input and output alphabets $\Sigma$ and $\Gamma$, a finite set
$\Delta \subseteq K \times \Sigma^* \times \Gamma^* \times K$ of transitions, an initial state $q_0$ and a set $F \subseteq K$
of accepting states. A computation is an infinite sequence of consecutive transitions
$(q_0, u_1, v_1, q_1), (q_1, u_2, v_2, q_2), \dots$; it is *successful* if some state of $F$ occurs infinitely often among the
$q_i$. Its input word is $u_1 u_2 \cdots$ and its output word is $v_1 v_2 \cdots$. The *infinitary rational relation*
$R(\mathcal{T}) \subseteq \Sigma^\omega \times \Gamma^\omega$ is the set of pairs $(u, v)$ of infinite words that are the input
and output words of a successful computation. Its domain and image are regular ω-languages, effectively computable from
$\mathcal{T}$.

**ω-rational functions.** $R(\mathcal{T})$ is *functional* if for every $u$ in its domain exactly one $v$ satisfies
$(u, v) \in R(\mathcal{T})$; it then defines a partial function $F_{\mathcal{T}} : \mathrm{Dom}(R(\mathcal{T})) \to \Gamma^\omega$,
an *ω-rational function*. Functionality of $R(\mathcal{T})$ is decidable (Gire).

**Continuity.** $\Sigma^\omega$ carries the prefix metric: $d(u, v) = 2^{-\ell}$ for $u \ne v$, where $\ell$ is the length of
their longest common prefix. A partial function $f$ is *continuous at* $x \in \mathrm{Dom}(f)$ if for every $n \ge 1$ there
is $k \ge 1$ such that $d(f(x), f(y)) < 2^{-n}$ whenever $d(x, y) < 2^{-k}$, for all $y \in \mathrm{Dom}(f)$. The *continuity
set* $C(f)$ is the set of points of $\mathrm{Dom}(f)$ at which $f$ is continuous; $f$ is continuous if $C(f) = \mathrm{Dom}(f)$.

Decision problems about these objects take Büchi transducers as input, coded by natural numbers.

## Depends on

- [Büchi acceptance condition](../../../../omega-automata-and-games/emptiness-of-b-chi-automata/mem-language-iff.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Whether an ω-rational function is continuous is decidable (Prieur). Many problems about infinitary rational relations,
such as universality, equivalence, inclusion, cofiniteness and unambiguity, are $\Pi^1_2$-complete (Finkel, earlier work).

## Sources

- O. Finkel, "Three applications to rational relations of the high undecidability of the infinite Post correspondence problem in a regular ω-language", *International Journal of Foundations of Computer Science* 23(7):1481–1497, 2012, doi:[10.1142/S0129054112400606](https://doi.org/10.1142/S0129054112400606). Numbering of the version read, arXiv:1107.5886v1: Definition 4.1 (Büchi transducers), the definitions of functional relations, ω-rational functions, the prefix metric and continuity sets in Section 4.2, Theorem 4.3 (Gire) and Theorem 4.4 (Prieur).
