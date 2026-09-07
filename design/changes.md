hacl-pulse is a reimplementation of HACL\* in idiomatic modern F\*/Pulse.

The overall goal is to reach feature-parity for C and F\* users.  API changes
are expected, and completely acceptable as long as they can be easily migrated.

# Specialization

hacl-pulse will use the new Custard extraction pipeline in F* that has built-in
support for specialization instead of using a custom tactic.  (gebner\_custard
branch in the fstarlang/fstar repo)

# Integer types

hacl-pulse will remove the `int_t` type and instead use
`{U,}Int{8,16,32,64,128}.t` directly.  We will add separate Secret32.t/etc.
types for integers that only expose constant-time operations.

For code that is parametric in the integer type, we will use type classes.

# Assembly code

hacl-pulse will no longer generate assembly code.  Instead, hacl-pulse will use
C intrinsics.  This removes the dependency on Vale.

The feasibility study in design/vale-migration shows that we can achieve
performance-parity with Vale-generated assembly code when using the clang
compiler.

# Array sizes

hacl-pulse will use SizeT.t for sizes (instead of the 32-bit sizes in HACL\*).
