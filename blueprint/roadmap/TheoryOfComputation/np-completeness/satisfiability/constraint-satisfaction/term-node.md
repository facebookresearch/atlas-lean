# Term nodes

A term node is stored as a triple $(\mathit{kind}, (a, b), \mathit{args})$ of natural numbers and a list of natural indices. In the intended reading it is a variable ($\mathit{kind} = 0$, variable $a$), an integer constant $a - b$ ($\mathit{kind} = 1$), or the function symbol $a$ applied to the earlier nodes listed in $\mathit{args}$ ($\mathit{kind} = 2$). The type also holds a node with tag $3$, or one whose arguments refer to a later index; legal tags, backward references and arities are conditions of [validation](well-formed-3.md).
