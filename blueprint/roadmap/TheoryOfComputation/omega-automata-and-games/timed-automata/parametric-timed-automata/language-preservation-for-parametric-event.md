# Language preservation for parametric event-recording automata is undecidable

No algorithm decides, given a parametric event-recording automaton and a reference parameter valuation, whether some other valuation yields the same untimed language, although event-recording automata are better behaved than timed automata without parameters.

**Theorem.** A *parametric event-recording automaton* (PERA) is a tuple $\mathcal A = (\Sigma, L, l_0, P, I, E)$ with a finite set $\Sigma$ of actions, a finite set $L$ of locations, an initial location $l_0$, a finite set $P$ of parameters, an invariant $I(l)$ for each location, and a finite set of edges $(l, g, a, l')$ with $a \in \Sigma$; guards and invariants are conjunctions of inequalities $x \bowtie \eta$ with $\bowtie \in \{<, \le, \ge, >\}$ and $\eta$ a parameter or an integer constant. There is one clock $x_a$ for each action $a$, and every transition labeled $a$ resets $x_a$. For a valuation $v : P \to \mathbb Q_{\ge 0}$, $v(\mathcal A)$ is the event-recording automaton obtained by replacing each parameter $p$ by $v(p)$, with the usual timed-transition semantics from $l_0$ with all clocks $0$. A run is *maximal* if it is infinite or cannot be extended by a discrete transition, and the untimed language $UL(v(\mathcal A))$ is the set of action sequences of maximal runs. The *language preservation problem* asks, given a PERA $\mathcal A$ and a reference valuation $v_0$, whether there is a valuation $v \neq v_0$ with $UL(v(\mathcal A)) = UL(v_0(\mathcal A))$. This problem is undecidable.

The proof needs only one parameter and four actions, and the problem stays undecidable when the language is defined by a Büchi or reachability acceptance condition or as the set of action sequences of all finite runs (Section 4.2 of the source). For parametric timed automata the corresponding undecidability was shown earlier by André and Markey, with all transitions labeled by one action; see also [language preservation for one-parameter timed automata](language-preservation-for-one-parameter-timed.md).

## Depends on

- [Timed automata over finite timed words](../decision-problems-for-timed-languages/timed-automata-over-finite-timed-words.md)
- [Parametric timed automata](parametric-timed-automata.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem of deterministic two-counter machines. One parameter $p$ and four actions $a_t, a_1, a_2, a_z$ with clocks $t, x_1, x_2, z$ encode a configuration: whenever $t = 0$, $x_1$ and $x_2$ equal the counter values, the clock $t$ is reset every $p$ time units, and $z$ counts the simulated steps so that the encoding blocks after $v(p) - 1$ steps. From a start location the automaton can move without guard to a location accepting every infinite word, can enter the simulation if $p > 0$, and has a further edge usable only if $p = 0$; the simulation leads on halting to a location accepting every infinite word. With $v_0(p) = 0$ the simulation is closed, so $UL(v_0(\mathcal A)) = \Sigma^\omega$. If the machine halts after $n$ steps, a valuation with $v(p) > n$ simulates it completely and again gives $\Sigma^\omega$. If it does not halt, every $v \neq v_0$ adds the finite run of the truncated simulation, which blocks and is therefore maximal, so $UL(v(\mathcal A)) \supsetneq \Sigma^\omega$.

## Sources

- É. André and S.-W. Lin, "The language preservation problem is undecidable for parametric event-recording automata", *Information Processing Letters* 136:17–20, 2018, doi:[10.1016/j.ipl.2018.03.013](https://doi.org/10.1016/j.ipl.2018.03.013); read as arXiv:1812.08948v1, whose numbering is used here: Definitions 1 and 2 and the definition of $UL$ (Section 2), the encoding of Section 3, Theorem 1 with its proof, and Section 4.2.
