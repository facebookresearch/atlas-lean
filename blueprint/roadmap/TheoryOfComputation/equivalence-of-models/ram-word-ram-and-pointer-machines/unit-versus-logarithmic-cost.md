# Repeated squaring separates unit-cost and logarithmic-cost RAM time

On a RAM with multiplication, the repeated-squaring program ($r \leftarrow 2$, then $n$ times $r \leftarrow r^2$, return $r = 2^{2^n}$) runs in $n$ steps under the **uniform (unit-cost)** model, in which every operation takes time $1$, but in time $1 + 2 + 4 + \dots + 2^n = 2^{n+1} - 1 = \Theta(2^n)$ under the **logarithmic-cost** model, in which the time of a step is the bit length of the largest operand involved; its space is $O(1)$ registers under the uniform model and $O(2^n)$ bits under the logarithmic model. For RAMs without multiplication (additive RAMs), time under the two measures is polynomially related.

## Proof sketch

The loop squares a register $n$ times; after squaring $i$ times the register holds $2^{2^i}$, whose bit length is $2^i + 1$. (Derived.) Since writing $2^{2^n}$ already costs at least its length $2^n + 1$ under logarithmic cost, any computation producing it costs at least $2^n$, so unit cost with multiplication is not polynomially related to logarithmic cost or to Turing-machine time.

## Depends on

- [Output of a RAM machine](../random-access-machines/ram-eval.md)

## Sources

- E. W. Mayr and H. Räcke, Efficient Algorithms and Data Structures (EADS), lecture slides, Technische Universität München, winter semester 2012/13, Part II "Foundations", Section 4 "Modelling Issues", slides 26–27 (uniform and logarithmic cost models; Example 2, RepeatedSquaring).
- Stephen A. Cook and Robert A. Reckhow, "Time Bounded Random Access Machines", Journal of Computer and System Sciences 7(4), 1973, Theorem 2 (additive RAMs).
