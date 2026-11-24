# Split Preorder go length sum

Assume that `V` carries a Boolean equality test `==` and a hash function.

The split preserves total length: the blocks' lengths sum to the preorder
length plus the pending block's length. The scanner's per-block work is
bounded by the blocks' total length, so this lemma is what turns the
second-preorder length into a scanner work bound.
