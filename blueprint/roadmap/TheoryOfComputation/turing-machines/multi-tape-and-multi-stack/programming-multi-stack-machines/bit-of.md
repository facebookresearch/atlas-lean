# Bit on top of a stack

Let $d$ be a decoder that reads each symbol either as a bit or as
a marker. For an optional symbol $o$ (the top of a stack, absent when the stack is empty), the
bit of $o$ under $d$ is $x$ when $o$ is a symbol that $d$ reads as the bit $x$, and false when $o$
is absent or $d$ reads it as a marker.
