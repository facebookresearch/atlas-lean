# Local confluence on words with one control symbol

Let $M$ be a single-tape machine with
finite tape alphabet and finite set of states, and let $w$ be a word over the symbols of its
rewriting system that contains exactly one control symbol (a state symbol or the halting symbol).
If $w$ rewrites in one step to $w_1$ and in one step to $w_2$ under the rules of $M$, then there is
a word $d$ such that $w_1$ rewrites to $d$ in at most one step and $w_2$ rewrites to $d$ in zero or
more steps.

Rewriting at a state symbol is deterministic, and the two erasures at the halting symbol commute.
