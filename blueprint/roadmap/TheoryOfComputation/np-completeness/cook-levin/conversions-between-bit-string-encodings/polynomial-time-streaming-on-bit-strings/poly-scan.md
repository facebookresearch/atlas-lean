# Poly Scan

If the state type `Q` is finite, `scan step finish q₀` is polynomial-time in the input length.
The machine stores output in reverse order and reverses it once at the end. Each transition emits
a bounded number of bits because the state and input alphabets are finite.
