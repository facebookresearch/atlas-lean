# The degeneralization counter reaches every higher value

Let $g$ be a generalized Büchi
automaton with acceptance sets $F_0, \dots, F_{k-1}$, and let $s$ be an infinite sequence of
states that visits every $F_j$ infinitely often, with counter sequence $c_0, c_1, \dots$. Then
for every time $n$ and every $j$ with $c_n \le j \le k$ there is a time $m \ge n$ with $c_m = j$.

The distance $d = j - c_n$ appears in the statement as a separate variable, and the proof is by
induction on $d$: the first visit to the awaited set after time $n$ advances the counter by one
(the counter stays put until then).
