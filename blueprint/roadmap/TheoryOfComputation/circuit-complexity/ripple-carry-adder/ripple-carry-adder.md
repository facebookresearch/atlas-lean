# Ripple-carry adder

The $n$-bit ripple-carry adder is the circuit with $2n + 1$ inputs,
$5n$ binary gates, each an XOR, AND or OR gate, and $n + 1$ outputs, built as follows. Write $a_i$
for input $i$, $b_i$ for input $n + i$ and $c_0$ for input $2n$, where $i < n$. For each $i < n$,
gates $g_{5i}, \dots, g_{5i+4}$ form a full adder for position $i$: $g_{5i} = a_i \oplus b_i$,
$g_{5i+1} = g_{5i} \oplus c_i$, $g_{5i+2} = a_i \wedge b_i$, $g_{5i+3} = g_{5i} \wedge c_i$ and
$g_{5i+4} = g_{5i+2} \vee g_{5i+3}$, where the carry $c_i$ is input $2n$ when $i = 0$ and gate
$g_{5i-1}$ otherwise. For $i < n$, output $i$ is gate $g_{5i+1}$, and output $n$ is the carry out
$c_n$: input $2n$ when $n = 0$, otherwise gate $g_{5n-1}$.
