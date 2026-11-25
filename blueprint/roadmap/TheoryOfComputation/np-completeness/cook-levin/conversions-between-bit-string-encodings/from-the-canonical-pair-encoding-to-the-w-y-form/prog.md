# Program of the pair-encoding converter

The program over the converter's four stacks,
five labels and states (a bit or nothing). Each pop either stores the popped bit in the state
(nothing if the stack is empty) or leaves the state unchanged, and each push of the stored bit
uses false when the state holds nothing.

At *read first*: pop the input, storing; if the state is true, pop the input twice without
storing, once storing and twice without storing, push the stored bit onto the first stash and go
to *read first*; otherwise go to *read second*. At *read second*: pop the input, storing; if the
state is true, pop the input once storing and once without storing, push the stored bit onto the
second stash and go to *read second*; otherwise go to *emit second*. At *emit second*: pop the
second stash, storing; if a bit was popped, push it onto the output as a right-tagged bit and go
to *emit second*; otherwise go to *separator*. At *separator*: push the separator onto the
output and go to *emit first*. At *emit first*: pop the first stash, storing; if a bit was
popped, push it onto the output as a left-tagged bit and go to *emit first*; otherwise halt.
