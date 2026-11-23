# Value of an appended flat gate

Let $c$ be a straight-line circuit with $k$ outputs, $g$ a flat gate whose references are all less than $k$,
and $x$ an input. If, for every $t < k$, output $t$ of $c$ carries the value $v_t$ (a list $v$ read with
default false), then the new output of $c$ with $g$ appended carries the flat value of $g$ computed from $v$
and $x$.
