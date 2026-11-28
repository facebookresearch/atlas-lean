# Instruction

An instruction is a natural triple `(op, x, y)`. The five valid opcodes mean `x ← y` (`op = 0`), `x ← x + 1` (`1`), `x ← 0` (`2`), `loop x` (`3`) and `end` (`4`), but the type is all of $\mathbb{N}^3$: an instruction with opcode `5` is representable.
