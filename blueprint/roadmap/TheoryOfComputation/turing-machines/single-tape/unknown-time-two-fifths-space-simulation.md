# Unknown-time one-writable-tape simulation in two-fifths-power space

Fix a finite input alphabet and a deterministic source with finite states and tape alphabet, a writable tape indexed by $\mathbb Z$, and finitely many read-only heads, all starting at zero. For input word $x$, the symbol oracle supplies the initial writable contents (tag absent) and the read-only symbols (one tag per read-only head) at each integer position. This oracle does not take the simulation cap. One transition reads the state and scanned symbols, writes at the writable head and moves each head by $-1,0,$ or $1$; a halting state freezes the configuration. The outcome after $T$ steps consists of the state and the Boolean halting flag.

Fix an accessor machine and real numbers $p,q\ge1$. For each given $(x,T)$ the access condition means that for every tag and every $|i|\le T$, on input $x$ and separate binary words for $T$, the tag number, the sign and magnitude of $i$, the accessor returns the oracle symbol in at most $p\log_2(T+2)^q$ work bits. The tag number uses a fixed enumeration. The accessor and simulator have finite control and finitely many writable two-way tapes with finite, possibly tape-dependent alphabets, initially blank, and separate read-only endmarked inputs. A run uses $\le b$ work bits if every visited work head lies in its tape's fixed window $[-l_j,h_j]$ throughout the run and the sum of window lengths times the corresponding symbol widths is $\le b$. For an alphabet of size $m$, the width is $\max(1,\operatorname{bitlength}(m-1))$.

There is one fixed finite-control simulator given only the read-only input word $x$, and constants $C>0$ and $e\in\mathbb N$. For every $x$ for which the accessor meets its polylogarithmic work-bit bound for every cap $T\ge2$, and every time $t$ at which the source reports its halting flag as true, this simulator halts with the source's state and true flag at time $t$, in at most $C(t+2)^{2/5}\log_2(t+2)^e$ work bits. Because source states freeze on halting, this includes the first halting time and every later time. No claim about behavior on nonhalting $x$ or a time bound is made.

## Depends on

- The cap-independent symbol oracle and finite workspace models above.

## Proof depends on

- [Capped two-fifths-space simulation](capped-two-fifths-space-simulation.md), a cap search yielding a cap within a constant factor of $t+2$, and reusable scratch-space bounds for the successive simulations.

## Expansion

Prove that caps can be supplied internally, workspace can be cleared or reused between trials, and outcome/state correctness survives moving from a sufficiently large cap to any halted time. Keep the access hypothesis uniform in all caps, not just one chosen after the actual halt.

## Sources

- OpenAI, [machine, accessor and unknown-time statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OneTapeSpace.lean#L11-L271).
