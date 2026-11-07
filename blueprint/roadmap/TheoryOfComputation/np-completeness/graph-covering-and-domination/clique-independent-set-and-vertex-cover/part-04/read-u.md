# The clique verifier's unary reader

For a stack $c$ and labels $\ell$ (its own) and
$\ell'$ (the next), the unary reader onto $c$ is the verifier statement that inspects the
input stack $X$ and sets the state to whether $X$ is empty: if it is, it goes to the rejecting
label; otherwise it pops the top symbol of $X$ and sets the state to whether that symbol is
the bit $1$; if so, it pushes the bit $1$ onto $c$ and goes to $\ell$, while any other symbol
(normally the terminating $0$) sends it to $\ell'$.

Run from $\ell$, it reads a unary number off $X$ onto the counter $c$.
