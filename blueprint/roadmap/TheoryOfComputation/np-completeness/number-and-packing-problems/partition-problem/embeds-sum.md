# Padding machine embeds the summation machine

The [padding machine](prog-3.md) contains the SUBSET-SUM summation machine: at the image of
every label of the summation machine under the [label map](sum-label.md), the padding machine's
instruction is that machine's instruction run on the [embedded stacks](sum-emb.md) with labels
renamed by the label map, except at the summation machine's halting labels.
