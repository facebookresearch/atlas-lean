# The built network evaluates the formula

Under assignment `σ`, the accumulator
node of the constructed network for `φ` evaluates to `φ.all (clauseVal σ)`: every clause
node reads its clause's value, and the AND chain collects them. The clause step needs the
duplicate-free root-index invariant (`coop_eval_coopClause_nodup`), which the construction
maintains.
