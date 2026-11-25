# Postorder encoding after a prefix

For a regular expression $r$ and a list $l$ of nodes,
the nodes of $r$ are appended after $l$ in postorder, by recursion on $r$. For $0$, $1$ and a
letter $a$, append the single node $0$, $1$ or $a$. For a sum $s + t$ (respectively a
concatenation $st$), append the nodes of $s$ after $l$, giving $l_1$, then the nodes of $t$ after
$l_1$, giving $l_2$, then a sum (respectively concatenation) node with arguments $|l_1| - 1$ and
$|l_2| - 1$. For a star $s^*$, append the nodes of $s$ after $l$, giving $l_1$, then a star node
with argument $|l_1| - 1$. The root of $r$ is the last node.
