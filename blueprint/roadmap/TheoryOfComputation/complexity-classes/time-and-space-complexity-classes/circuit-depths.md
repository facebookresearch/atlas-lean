# Gate depths of a flat Boolean circuit

For a circuit given as a list of gates
$g_0, \dots, g_{m-1}$, the list of gate depths is $(d_0, \dots, d_{m-1})$, where $d_j = 0$ if
$g_j$ is an input or constant gate, and otherwise $d_j$ is one more than the maximum of the
depths $d_a$ of the gates $a$ that $g_j$ references (the maximum over no references is $0$),
a reference $a \ge j$ counting as depth $0$.
