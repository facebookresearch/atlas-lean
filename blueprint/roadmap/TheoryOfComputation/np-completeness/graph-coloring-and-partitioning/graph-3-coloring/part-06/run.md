# Correctness and step bound of the 3-COLOR emitter

Let $\varphi$ be a CNF formula
with token list $t(\varphi)$, let $o$ be a bit list and $v$ a Boolean. Started at its start
label with local state $v$, with the token stack holding $t(\varphi)$ reversed, the output
stack holding $o$ and every other stack empty, the emitter machine reaches the label
$\mathsf{done}$ within $500\,(|t(\varphi)| + 1)^4$ steps, in some local state and with some
stacks whose output stack holds the 3-COLOR instance of $\varphi$ followed by $o$ (read
top-first).
