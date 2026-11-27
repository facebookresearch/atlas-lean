# Strategy improvement for parity games

There is a strategy improvement algorithm that solves finite [parity games](../parity-games/parity-game.md) in exponential time. Eve is given an extra
move that stops the play. A stopped play is evaluated by the vector in $\mathbb{N}^d$ counting the occurrences of each priority and an
infinite play by a top element $\top$; vectors are compared at the largest priority where they differ, more occurrences being better
for an even priority and worse for an odd one, and $\top$ is greatest. A positional strategy $\sigma$ of Eve has value
$\mathrm{val}_\sigma(v) = \inf_\tau$ of the evaluation of the play from $v$, and the algorithm only uses strategies all of whose infinite plays
satisfy parity, starting from the strategy that always stops, after first removing the attractor of Adam to the cycles among his own vertices
whose largest priority is odd (on those vertices he wins). An edge $u \xrightarrow{p} v$ is *improving* if extending $\mathrm{val}_\sigma(v)$ by $p$
gives more than $\mathrm{val}_\sigma(u)$. Switching any nonempty set
of improving edges yields a strategy whose value is at least as large everywhere and strictly larger somewhere (progress), and a
strategy without improving edges is optimal and wins from exactly Eve's winning region (optimality). Since there are finitely
many positional strategies the algorithm terminates. The first discrete strategy improvement for parity games is due to Vöge and
Jurdziński; Friedmann constructed exponential lower bounds for many switching rules.

## Depends on

- [Parity game](../parity-games/parity-game.md)

## Proof depends on

- [Finite parity games are positionally determined](../parity-games/finite-parity-games-are-positionally-determined.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Section 2.3, Theorem 2.3 with Lemmas 2.4–2.7 (progress and optimality), and the bibliographic references at the end of the chapter, crediting the first discrete strategy improvement algorithm to J. Vöge and M. Jurdziński (CAV 2000) and the exponential lower bounds to O. Friedmann.
