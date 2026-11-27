# The host on the real generators of a machine

Let $M$ be a finite multi-stack Turing
machine with encoding data $E$, let $Y$ be a list of input symbols, and let $\mathit{acc}$ be an
output symbol. This is the host program whose five generators are the real ones for $M$. The
update generator is the family generator of $E$ for the (label, state) codes, window codes and
next (label, state) codes of the situations of $E$. The situation-definition generator is the
family generator of $E$ for the same (label, state) codes and window codes, with the positions of
the situation variables in place of the next codes. The shift generator is the one of $E$. The
accept generator is the one for the number of (label, state) codes, the code of the halted label
with the initial internal state, the number of the output stack, and the code of $\mathit{acc}$
on the output stack. The init generator is the one for the code of the start label and initial
state of $M$, the number of the input stack, and the sorted distinct codes of the symbols of $Y$.
The input itself is not a parameter: the init generator reads it from the host's input-code
stack.
