# Location of an instruction target

Under an assignment $f$ of locations to instructions and variables, the target location of instruction $I_i$ is $f(g(I_i))$, where a target with tag $0$, namely $(0, j)$, names instruction $I_{j+1}$ and a target with any nonzero tag names variable $j$; an index $j$ out of range gives location $0$.
