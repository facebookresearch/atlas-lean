# Recursive hybrid automata and their reachability games

A recursive hybrid automaton is a recursive state machine whose components carry real-valued variables evolving at constant rates;
calls to components pass some variables by value and the others by reference, and reachability games are played on its
configuration graph.

**Syntax.** A *recursive hybrid automaton* (RHA) $\mathcal{H} = (X, (\mathcal{H}_1, \dots, \mathcal{H}_k))$ has a finite set $X$ of
real-valued variables and components $\mathcal{H}_i = (N_i, \mathit{En}_i, \mathit{Ex}_i, B_i, Y_i, A_i, \delta_i, P_i, \mathit{Inv}_i, E_i, J_i, F_i)$
where

- $N_i$ is a finite set of nodes containing disjoint sets $\mathit{En}_i$ of entry nodes and $\mathit{Ex}_i$ of exit nodes;
- $B_i$ is a finite set of boxes and $Y_i : B_i \to \{1, \dots, k\}$ maps each box to the component it invokes; a box $b$ has call ports
  $(b, en)$ for the entries $en$ and return ports $(b, ex)$ for the exits $ex$ of component $Y_i(b)$, and the locations $Q_i$ of
  $\mathcal{H}_i$ are its nodes, call ports and return ports;
- $A_i$ is a finite set of actions and $\delta_i : Q_i \times A_i \to Q_i$ the transition function, with no transitions out of call ports
  and exit nodes;
- $P_i : B_i \to 2^X$ gives the variables passed by value to each box, the others being passed by reference;
- $\mathit{Inv}_i : Q_i \to \mathrm{Rect}(X)$ gives invariants and $E_i : Q_i \times A_i \to \mathrm{Rect}(X)$ enabling conditions, where
  rectangular constraints are conjunctions of $x \bowtie c$ with $c \in \mathbb{Z}$;
- $J_i : A_i \to 2^X$ gives the variables reset to $0$ by each action, and $F_i : Q_i \to \mathbb{N}^{|X|}$ the rate of each variable in
  each location.

An RHA is *glitch-free* if every box passes either all variables or none by value, and *hierarchical* if the components can be
ordered so that no component invokes a component of the same or higher order. A variable is a *clock* if its rate is $1$ in every
location and a *stopwatch* if its rate is always $0$ or $1$. A *recursive timed automaton* (RTA) has only clocks; a *recursive
stopwatch automaton* (RSA) has only stopwatches.

**Semantics.** A configuration $(\kappa, q, \nu)$ has a call stack $\kappa \in (B \times \mathbb{R}^X)^*$, a location $q$ and a valuation
$\nu$ satisfying $\mathit{Inv}(q)$. At a call port $(b, en)$ the automaton pushes $(b, \nu)$ and moves to $en$ without delay; at an exit
$ex$ it pops $(b, \nu'')$, moves to $(b, ex)$ without delay and restores the variables in $P(b)$ to their values in $\nu''$. Elsewhere a
timed action $(t, a)$ lets time $t$ pass at rates $F(q)$, with the invariant satisfied throughout and $E(q, a)$ satisfied at the end,
then takes the transition $\delta(q, a)$ and resets the variables in $J(a)$.

**Games.** A partition of the locations into those of two players, Achilles and the tortoise, gives a game arena. The *reachability
game problem* asks, for an initial location and valuation with empty stack and a set of final locations, whether Achilles has a
strategy that reaches a final location against every strategy of the tortoise; under *bounded time*, the final location must be
reached within total time $T \in \mathbb{N}$. An instance is finite: the automaton, the partition, the final locations, and an initial valuation with rational entries (the source writes $\nu \in \mathbb{R}^{|X|}$, which is not a finite input).

## Depends on

- [Timed games](../timed-games.md)

## Proof depends on

None.

## Sources

- S. N. Krishna, L. Manasa and A. Trivedi, "Improved undecidability results for reachability games on recursive timed automata", in *GandALF 2014*, Electronic Proceedings in Theoretical Computer Science 161, pp. 245–259, 2014, doi:10.4204/EPTCS.161.21; Section 3 of the version arXiv:1408.5968v1 (the definition of recursive hybrid automata, glitch-free and hierarchical automata, clocks and stopwatches, the semantics, and the reachability and time-bounded reachability game problems) and Section 2 (recursive state machines).
