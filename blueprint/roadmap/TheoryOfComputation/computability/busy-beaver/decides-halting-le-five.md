# ZFC-like theories decide halting through five states

For every ZFC-like presentation
$Z$ and every $n \le 5$, the theory presented by $Z$ decides halting for $n$-state machines: for
every $n$-state machine it proves the machine's halting sentence or its non-halting sentence.

Proof idea: let $S$ be Rado's shift function; $Z$ proves the runtime bound $S(n)$ for
halting $n$-state machines. Run each machine for $S(n)$ steps; if it has halted, the
computation verifies, and if it has not, the bound derives its non-halting sentence.
