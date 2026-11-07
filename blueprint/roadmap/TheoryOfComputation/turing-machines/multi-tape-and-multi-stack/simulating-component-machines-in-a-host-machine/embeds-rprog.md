# The reduction host embeds the component

Let $c$ be a component machine with stacks
$c_X$ and $c_O$, a map $g_X$ from bits to the alphabet of $c_X$, and labels $s$ and $d$,
and suppose that $c$ halts at $d$. Rename the labels of $c$ by sending $d$ to the cleanup label
with answer false and every other label $l$ to the host's copy of $l$, and embed the stacks of
$c$ as the host's copies over the bit input alphabet. Then the reduction host built from
$c_X$, $c_O$, $g_X$, $s$ and $d$ embeds $c$: for every label $l$ of $c$, either $c$ halts at
$l$, or the host's statement at the renamed label of $l$ is the statement of $c$ at $l$ with
stacks and labels translated.
