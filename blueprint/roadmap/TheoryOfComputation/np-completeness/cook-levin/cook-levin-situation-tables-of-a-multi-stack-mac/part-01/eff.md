# Symbolic effect of a statement tree

Let $W$ assign to each stack $k$ a window $W_k$, a
list of cells each holding a symbol or $\bot$. The window top of stack $k$ for pushed lists $P$
and consumption counts $c$ is the head of $P_k$ if $P_k$ is nonempty, and otherwise the entry of
$W_k$ at position $c_k$ (counting from $0$), or $\bot$ if there is none. The effect of a statement
tree $q$ from a state $v$, pushed lists $P$ and consumption counts $c$ is a label (or none), a
state, pushed lists and consumption counts, defined by recursion on $q$: a push onto stack $k$
prepends the symbol computed from $v$ to $P_k$ and continues; a peek on stack $k$ replaces $v$ by
the state computed from $v$ and the window top of $k$ and continues; a pop on stack $k$ does the
same, also removes the head of $P_k$ (if any), and increases $c_k$ by one if $P_k$ was empty;
a load replaces $v$ by the state computed from $v$ and continues; a branch continues with the
subtree selected by $v$; a goto returns the label computed from $v$, and a halt returns no
label, each together with the current $v$, $P$ and $c$.

Thus $P_k$ holds the symbols pushed in this step and still on top, and $c_k$ counts the original
symbols consumed, a push followed by a pop cancelling.
