# Correctness and running time of the HAMPATH emitter

Let $\varphi$ be a CNF formula with
token sequence $\mathrm{toks}(\varphi)$, let $o$ be a list of bits, and let $S$ be stacks in which
the token stack $T$ holds $\mathrm{toks}(\varphi)$ reversed, the output stack $O$ holds $o$, and
every other stack is empty. Then for every internal bit $v$ there are an internal bit $v'$ and
stacks $S'$ such that the emitter goes, in at most $2000(|\mathrm{toks}(\varphi)| + 1)^5$ steps,
from its start label with bit $v$ and stacks $S$ to label $\mathsf{done}$ with bit $v'$ and stacks
$S'$, and the output stack of $S'$ is Sipser's HAMPATH instance for $\varphi$ followed by $o$
(so the instance is read top-first).
