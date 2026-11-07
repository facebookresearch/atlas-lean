# Embedded list canonicalizer preserves outside stacks

Embed the concrete normalizer in a caller, preserving every stack
outside its workspace on both success and failure. Entry requires clean
scratch and output stacks. After `bad`, clear partial workspace data
before another invocation.
