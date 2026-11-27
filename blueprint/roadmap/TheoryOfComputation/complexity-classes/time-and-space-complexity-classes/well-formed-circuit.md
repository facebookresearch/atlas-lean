# Well-formed flat circuits

A flat Boolean circuit on $n$ inputs, given as a list of
gates $(g_0, \dots, g_{m-1})$, is well-formed when every gate references only strictly earlier
gates: for every $j < m$, every gate index $a$ among the inputs of $g_j$ satisfies $a < j$.
