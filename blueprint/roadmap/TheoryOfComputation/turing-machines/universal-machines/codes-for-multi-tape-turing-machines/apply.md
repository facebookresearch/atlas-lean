# Applying a coded action

Given an input word $x$, a coded action $a$ and an explicit
configuration $e$, applying $a$ to $e$ gives the configuration whose state is the next state of
$a$; whose input head position is that of $e$, say $p$, moved by the coded input move of $a$,
where a left move gives $p - 1$ (truncated at $0$), staying gives $p$, and a right move gives
$\min(p + 1, |x| + 1)$; whose work tape $i$ is work tape $i$ of $e$ after writing the optional
symbol of $a$ for tape $i$ under the head and then moving the head by the coded move of $a$ for
tape $i$; and whose output is the output of $e$ followed by the output bit of $a$, if any.
