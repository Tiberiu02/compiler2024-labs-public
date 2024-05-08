---
title: Project Proposal Group 23
geometry: left=2cm, right=2cm, top=2cm, bottom=2cm
---

# [7] LLVM Code Generation (2 points)

This extension will involve modifying the code-generation stage of the compiler
that we have been working on throughout the semester; namely, extending the 
`CodeGenerator` class to output LLVM-IR instead of WebAssembly.

We don't see this implementation affecting any other stage in the compilation 
process before code-generation.

For example, given the following Alpine program

```
fun square(_ x: Int) -> Int {
    x * x
}
```

we should be able to output LLVM IR similar to

```
define i32 @square(i32) local_unnamed_addr #0 {
    %2 = mul nsw i32 %0, %0
    ret i32 %2
}
```

We will start with primitive types and records as we did in WebAssembly 
code-gen, and extend if possible once we have a better grasp of the scope.

# [4] Methods (1 point)

For this, we would like to be able to use *standard* method syntax as we would
expect to see in any other programming language with methods. Such as 
`a.insert(1).insert(2)` as described in `proposals.md`.

This syntax does not introduce any new symbols that aren't already present in 
the language, and hence won't require any changes to the lexer. If we follow 
the implementation hint described in `proposals.md` which involves de-sugaring
a method into a free function, the only changes required will be in the parser.

