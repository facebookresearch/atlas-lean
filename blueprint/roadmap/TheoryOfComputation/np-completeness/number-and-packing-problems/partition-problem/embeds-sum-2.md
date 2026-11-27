# Membership transducer embeds the summation machine

The [membership transducer](prog-5.md) contains the SUBSET-SUM summation machine: at the image of
every label of the summation machine under the [label map](sum-label-2.md), the transducer's
instruction is that machine's instruction run on the [embedded stacks](sum-emb-2.md) with labels
renamed by the label map, except at the summation machine's halting labels.
