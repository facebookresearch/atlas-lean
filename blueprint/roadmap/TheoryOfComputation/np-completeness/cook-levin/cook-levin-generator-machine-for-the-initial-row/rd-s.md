# Read test for one code

Given labels $\mathrm{hit}(i)$ and $\mathrm{miss}(i)$ for the
codes $i < g$, the read test for code $i$ is the statement, on a counter machine's stacks plus an
input stack of codes, that peeks at the top of the input stack and sets the flag to whether it
equals $i$. If it does, the test pops it and goes to $\mathrm{hit}(i)$; otherwise (including when
the input stack is empty) it goes to $\mathrm{miss}(i)$.
