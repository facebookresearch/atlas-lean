# Embedded pair-frame splitter preserves caller stacks

Let $M$ be a multi-stack Turing machine with Boolean internal state, stacks $J$ and labels $L$, and suppose it
contains the [pair-frame splitter](prog.md) through a stack embedding $E$ (an injective map from the splitter's
three stacks to stacks of $M$, with a bijection between the corresponding alphabets) and a label map $\varphi$: at
every label $\ell$ where the splitter does not halt, the statement of $M$ at $\varphi(\ell)$ is the splitter's
statement at $\ell$ transported along $E$ and $\varphi$.

Let $x$ be a bit string, $v$ a Boolean and $S$ stack contents of $M$ whose embedded stacks hold input $x$ and empty
left and scratch stacks. Then there are an internal state $v'$ and stack contents $T$ such that

- $M$ goes from label $\varphi(\text{read})$, internal state $v$ and stacks $S$ to label $\varphi(\text{good})$ if
  some prefix of $x$ is the framed form of a bit string and to $\varphi(\text{bad})$ otherwise, with internal state
  $v'$ and stacks $T$, in at most $|x| + 1$ steps;
- $T$ and $S$ agree on every stack of $M$ outside the image of $E$;
- if $x$ is the framed form of $p$ followed by $r$, then the embedded stacks of $T$ hold input $r$, left stack $p$
  and an empty scratch stack.
