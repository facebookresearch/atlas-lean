# A forced two-step max-plus elimination returns a nonoptimal solution

Use triples of coefficients in $\mathbb R\cup\{-\infty\}$, evaluated at $w=(x,y,z)$ as $E_f(w)=\max_k(f_k+w_k)$. A row $(l,r)$ requires $E_r(w)\le E_l(w)$. Initially the two rows are $\max(x,y)\ge z$, $x\ge\max(y+1,z-2)$, the cost is $x$ and both variables $x,y$ remain; the third coordinate is not eliminated. For either ordering of distinct rows $i,r$ and every real $\alpha$, there is a real triple with $E_{l_i}(w)<\alpha+E_{r_r}(w)$.

For a remaining column $j$, row $i$ is a lower row if $l_{ij}$ is finite and $r_{ij}<l_{ij}$, and upper if $r_{ij}$ is finite and $l_{ij}<r_{ij}$. A column is dominating when it has both. An eligible pair uses a lower row for a remaining column, and must use a dominating column if one exists. A state is well formed if eliminated coefficients are all $-\infty$, and bounded if each remaining column has a lower or upper row. It stops when $r_{i2}\le l_{i2}$ for both rows. If not stopped, failure means no remaining column or no lower or upper row on any remaining column. The switch case is the nonstopped case with remaining columns all absent from the cost, no lower row on them, and at least one upper row.

For an eligible pair form $g_j=-\infty$ and $g_k=r_{ik}-l_{ij}$ for $k\ne j$. Set coefficient $j$ of each row-side and the cost to $-\infty$ after replacing each other coefficient $f_k$ by $\max(f_k,f_j+g_k)$. Delete the column from the remaining set, and replace a row by two all-$-\infty$ forms if its new right coefficients are componentwise at most its new left coefficients.

The first eligible pair is uniquely row $0$, column $1$ (zero-based), yielding an empty row $0$, row $1$ equal to $x\ge z+1$, cost $x$ and just $x$ remaining. The next pair is uniquely row $1$, column $0$, yielding two empty rows, cost $z+1$ and no remaining columns; the stop condition holds. Both steps start well formed and bounded, and start in none of stop, switch, or failure; they preserve well-formedness and each has at least one finite substituted cost coefficient. With $z=0$, reconstruction by the selected lower forms gives $(1,0,0)$, feasible in the initial rows and with initial cost equal to the final cost there. The triple $(0,-1,0)$ is also feasible and has strictly smaller initial cost than that final cost at $(1,0,0)$.

## Related topics

- [Mean-payoff game solvability](../../omega-automata-and-games/polynomial-time-solvability-of-mean-payoff-games.md) concerns a different problem; the finite certificate here tests a proposed max-plus optimization step, not its algorithmic complexity.

## Sources

- OpenAI, [TruffetCounterexample.lean, model and `finite_execution_not_optimal`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TruffetCounterexample.lean#L8-L129).
