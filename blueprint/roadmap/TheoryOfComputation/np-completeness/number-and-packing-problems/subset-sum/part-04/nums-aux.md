# Parsing number blocks, with fuel

For a fuel $n$ and a list of bits $r$, the result is
either a list of numbers or a failure. If $r$ is empty, the result is the empty list. If $r$ is
non-empty and $n = 0$, parsing fails. If $r$ is non-empty and $n = m + 1$, one prefix-coded
number is decoded off the front of $r$: if this gives a number $a$ with remainder $r'$, the result
is $a$ followed by the result for $r'$ with fuel $m$ (failing if that fails), and otherwise
parsing fails. Here the prefix code of $a$ is the canonical binary code of $a$, least significant
bit first, with each bit $b$ written as the pair true, $b$, followed by a final false.
