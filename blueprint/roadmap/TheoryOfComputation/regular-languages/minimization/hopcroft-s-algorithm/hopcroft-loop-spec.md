# Termination of Hopcroft's loop

Let $M$ be a DFA with finite state set $Q$ over a finite
alphabet $\Sigma$, let $P$ be a partition of the states given as a list of blocks, let $W$ be a
waiting list of splitters, and let $k$ be a natural number. If $P$ and $W$ satisfy the invariants
of Hopcroft's loop and $|W| + |\Sigma| \cdot (|Q| - |P|) \le k$, where $|P|$ and $|W|$ are the
lengths of the lists, then Hopcroft's loop run from $(P, W)$ with a budget of $k$ rounds ends with
an empty waiting list, and the partition and waiting list it returns again satisfy the invariants.

The invariants make $P$ a partition into nonempty blocks, so $|P| \le |Q|$ and the difference
$|Q| - |P|$ is not truncated.
