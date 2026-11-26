# Horn formulas with a given model set

A CNF formula $\varphi$ is a Horn formula on the $n$ variables with model list $M'$ when every clause of $\varphi$ contains at most one distinct positive literal, every literal uses a variable below $n$, and for every truth assignment $a$ to the $n$ variables, $a$ satisfies $\varphi$ exactly when the list of its values is an entry of $M'$. Only length-$n$ entries of $M'$ are compared with assignments; entries of other lengths are never models.
