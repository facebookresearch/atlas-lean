# Clocked evaluator

The clocked evaluator runs a code $c$ on a binary input $x$ for $T$
steps: it applies the evaluator's step $T$ times to the initial explicit configuration. If the
resulting configuration is halted, it returns that configuration's output; otherwise it
returns no result.
