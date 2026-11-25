# Payload normalization is polynomial-time

The [normalization](../normalizing-the-total-binary-natural-number-deco/normalize-nat.md) of bit strings, as a
function from bit strings to bit strings, is computable in polynomial time by a finite multi-stack Turing machine,
where a bit string $c_1 \cdots c_m$ is given to the machine, and returned by it, as its canonical binary code
$1 c_1 0\, 1 c_2 0 \cdots 1 c_m 0$ (each bit as a self-delimiting block).
