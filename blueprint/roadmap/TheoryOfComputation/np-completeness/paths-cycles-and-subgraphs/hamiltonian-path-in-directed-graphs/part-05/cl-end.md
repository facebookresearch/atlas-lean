# End of a clause in the detour walk

For booleans $p_p$ and $p_n$ (the flags recording
whether the current clause contains the current variable positively, respectively negatively),
the detour walk continues at the end of the clause at the label where the first positive detour
site $d_{1u}$ starts with passed bit $p_n$ if $p_p$ is true; otherwise, if $p_n$ is true, at the
label where the first negative detour site $d_{3u}$ starts with passed bit false; and otherwise at
the label that ends the clause.
