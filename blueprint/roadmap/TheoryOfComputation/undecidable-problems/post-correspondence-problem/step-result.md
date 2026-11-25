# A rewrite at the control symbol

Let $M$ be a single-tape machine with finite tape
alphabet and finite set of states. Let $x$ be a control symbol (a state symbol or the halting
symbol $H$) and let $u$ and $v$ be words that contain no control symbol. If $u\,x\,v$ rewrites in
one step to $w'$ under the rules of $M$, then either $x$ is a state symbol $q$ and the successor of
$u\,q\,v$ under the rules for $q$ is defined and equals $w'$, or $x = H$ and either $u = u'\,c$ for
a word $u'$ and a tape symbol $c$ with $w' = u'\,H\,v$, or $v = c\,v'$ for a tape symbol $c$ and a
word $v'$ with $w' = u\,H\,v'$.
