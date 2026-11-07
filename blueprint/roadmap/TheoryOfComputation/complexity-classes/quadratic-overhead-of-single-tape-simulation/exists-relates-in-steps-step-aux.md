# Running one statement on the emulator

Let $M$ be a multi-stack machine and $N$ a
statement over the same stack alphabets, labels and internal states, and write $|N|$ for the
structural size of $N$. Let $H \in \mathbb{N}$, let $v$ be an internal state, let $S$ be a
family of stacks $S_k$, each of height at most $H$, and let $L$ be tape contents whose $k$-th
track lists $S_k$ from bottom to top, for every $k$. Running the translation of $N$ in the
$\mathrm{TM1}$ emulator of $M$ from state $v$, with the head at the bottom marker of $L$, gives
a configuration that reaches, in some number $m \le |N| (2 (H + |N|) + 2)$ of emulator steps,
a configuration representing the result of running $N$ from state $v$ on the stacks $S$: it
has the corresponding label and the same internal state, and its head is at the bottom marker
of a tape whose $k$-th track lists the $k$-th resulting stack from bottom to top.
