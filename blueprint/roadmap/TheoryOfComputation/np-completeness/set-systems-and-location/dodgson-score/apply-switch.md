# Apply Switch

Apply the switch $(v, p)$: replace voter $v$'s ballot by the [switch at position $p$](switch-at.md), which exchanges the entries at positions $p$ and $p + 1$ when both exist. At the last position the result is not an exchange: a missing right entry reads as $0$ and the write past the end does nothing, so switching $[0, 1]$ at position $1$ gives $[0, 0]$. A voter index out of range leaves the ballots unchanged.
