# Membership transducer embeds the doubling machine

The [membership transducer](prog-5.md) contains the [doubling machine](prog.md): at the image of
every label of the doubling machine under the [label map](double-label.md), the transducer's
instruction is the doubling machine's instruction run on the [embedded stacks](double-emb.md) with
labels renamed by the label map, except at the doubling machine's halting label.
