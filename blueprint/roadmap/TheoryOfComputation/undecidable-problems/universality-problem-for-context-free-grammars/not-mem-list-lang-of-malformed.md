# Malformed words are in no list language

Let $P$ be a list of dominoes and $s$ a map from
dominoes to words (in use, the top or the bottom). Write the code of an index $i$ as the bits
$|\,1^i$, where $|$ stands for the bit true and $1$ for the bit false. A word over letters and
bits that is malformed with respect to $|P|$ (it has no bits, its first bit is a $1$, a bit is
followed by a letter, or it contains the factor $|\,1^{|P|}$) does not belong to the list
language of $s$ for $P$.
