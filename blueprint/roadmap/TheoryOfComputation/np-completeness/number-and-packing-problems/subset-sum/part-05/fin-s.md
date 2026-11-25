# Carry step of the SUBSET-SUM verifier

For a carry bit $c$, the verifier statement that
carries $c$ through the rest of the sum on stack $A$: if $A$ is empty, it sets the local variable
to true, pushes the bit $1$ onto $B$ when $c$ is true and goes to label $\mathrm{back}$; otherwise
it pops the top symbol of $A$, read as a bit $a$ (a symbol that is not a bit reads as $0$), sets
the local variable to $a$, pushes the bit $a \oplus c$ onto $B$ and goes to label
$\mathrm{fin}(a \wedge c)$.
