# Capped one-writable-tape simulation in two-fifths-power space

Fix a finite input alphabet and a deterministic source with finite states and tape alphabet, a writable tape indexed by $\mathbb Z$, and finitely many read-only heads, all starting at zero. For input word $x$, the symbol oracle supplies the initial writable contents (tag absent) and the read-only symbols (one tag per read-only head) at each integer position. This oracle does not take the simulation cap. One transition reads the state and scanned symbols, writes at the writable head and moves each head by $-1,0,$ or $1$; a halting state freezes the configuration. The outcome after $T$ steps consists of the state and the Boolean halting flag.

Fix an accessor machine and real numbers $p,q\ge1$. For each given $(x,T)$ the access condition means that for every tag and every $|i|\le T$, on input $x$ and separate binary words for $T$, the tag number, the sign and magnitude of $i$, the accessor returns the oracle symbol in at most $p\log_2(T+2)^q$ work bits. The tag number uses a fixed enumeration. The accessor and simulator have finite control and finitely many writable two-way tapes with finite, possibly tape-dependent alphabets, initially blank, and separate read-only endmarked inputs. A run uses $\le b$ work bits if every visited work head lies in its tape's fixed window $[-l_j,h_j]$ throughout the run and the sum of window lengths times the corresponding symbol widths is $\le b$. For an alphabet of size $m$, the width is $\max(1,\operatorname{bitlength}(m-1))$.

There exist one fixed simulator, a natural $e$ and a real $C>0$ such that for all words $x$ and all $T\ge2$ satisfying that access condition, the simulator on $x$ with a separate binary input $T$ halts with the outcome after exactly $T$ source steps and uses at most $CT^{2/5}\log_2(T+2)^e$ work bits. The source need not halt by $T$, and there is no time bound for the simulator.

## Depends on

- A deterministic one-writable-tape transition system and the read-only oracle/access and window-bit model above. Arbitrary initial contents cannot be replaced by a blank-tape assumption.

## Proof depends on

- A capped simulation construction covering all positions reachable through time $T$, including access calls and accumulation of workspace through nested subcomputations.

## Expansion

Separate finite transition-table simulation from the cap-dependent accessor contract. Prove the head-window invariant, bit-width cost accounting, outcome correctness including frozen halting, and compilation of the cap as a read-only argument.

## Sources

- OpenAI, [OneTapeSpace.lean, machine and access definitions, and `capped`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OneTapeSpace.lean#L11-L263).
