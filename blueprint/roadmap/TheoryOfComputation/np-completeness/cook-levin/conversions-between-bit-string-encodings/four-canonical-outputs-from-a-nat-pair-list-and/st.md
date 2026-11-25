# Stack invariant of the four-output pair-list decoder

For bit strings $i$, $x$, $o_w$, $o_v$, $o_c$, $o_t$, the stack contents $\mathrm{st}(i, x, o_w, o_v, o_c, o_t)$ of
the [four-output decoder](prog.md) put $i$ on the input of the item workspace, $o_w$ and $o_v$ on its first and
second outputs (weights and values), $x$ on the splitter input of the final pair workspace, $o_c$ and $o_t$ on its
left and right outputs (capacity and threshold), and leave every other stack empty. At entry the item input is
empty and the whole input $x$ lies in the final pair workspace.
