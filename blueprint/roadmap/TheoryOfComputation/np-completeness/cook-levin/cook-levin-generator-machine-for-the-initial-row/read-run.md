# The read chain

Let $M'$ be a machine on a counter machine's stacks plus an input stack of
codes $< g$, with labels $\mathrm{rd}(i)$, $\mathrm{hit}(i)$ and $\mathrm{miss}(i)$ for $i < g$,
such that at $\mathrm{rd}(i)$ it runs the read test for code $i$ with these hit and miss labels,
and $\mathrm{miss}(i) = \mathrm{rd}(i + 1)$ whenever $i + 1 < g$. Then for all counter stacks $S$,
codes $c$, input lists $xs$, all $k$ and codes $i$ with $i + k = c$, and every flag $v$, the
machine $M'$ goes in exactly $k + 1$ steps from label $\mathrm{rd}(i)$, flag $v$, stacks $S$ and
input $c$ followed by $xs$ to label $\mathrm{hit}(c)$, flag true, stacks $S$ and input $xs$.
