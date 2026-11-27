# Deterministic, one-sided and two-sided logarithmic space in a transition-table model

Use finite transition-table machines on binary words with finitely many read-only input heads, clipped to the two end markers, and finitely many two-way writable Boolean tapes initially all zero. Heads start at the left end marker or at work cell $0$ respectively and move by at most one per step. A step can read one indexed coin bit. The control has halting Boolean output labels, and configurations freeze there. The workspace bound, for every word, every coin tape and every prefix through time $t$, is $c\lceil\log_2(|x|+2)\rceil$, for some positive integer $c$, on the sum over work tapes of the numbers of distinct visited head positions.

In this model $\mathsf L=\mathsf{RL}$ and $\mathsf{RL}=\mathsf{BPL}$ as sets of binary languages. In $\mathsf L$ the transition ignores the coin, and on each word some time has the correct halting bit. In the two randomized classes there must be a clock $C(|x|+2)^d$ with positive integer $C$ and natural $d$, and halting by that clock for every coin tape. Acceptance probability is the fraction of uniformly chosen prefixes of the clock length that give halting output true. For $\mathsf{RL}$ it is at least $1/2$ on yes-inputs and zero on no-inputs; for $\mathsf{BPL}$ the respective bounds are at least $2/3$ and at most $1/3$.

## Depends on

- The read-only/work-tape transition system and acceptance-probability conventions defined above.

## Proof depends on

- A small-space evaluator for finite recognizers, including the uniform acceptance-probability estimator and its exact decision threshold in this tape and clock model. The easy inclusions and the reverse inclusions need different arguments.

## Expansion

Give a native bridge tracking input heads, work-cell accounting, and freezing after halt. Provide coin-prefix counting in the randomized model and prove the necessary inclusions separately. Do not substitute pseudorandom-generator seed length, simulation time or uniformity claims for equality of the specified sets of languages.

## Related topics

- [Deterministic log space](log-space.md) uses a different machine representation; comparison requires work-cell and transition simulation.

## Sources

- OpenAI, [LogspaceEquality.lean, machine, classes and equality](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LogspaceEquality.lean#L9-L138).
