# Diktor

Diktor is a bootstrap interpreter of the Keleut programming language, written in OCaml.
It implements parse → type inference → tree-walking evaluation, and serves as the
test oracle for the future self-hosted Keleut compiler.

This repository started life (2018-2019) as a frontend for the Orphos programming
language and was rebooted in 2026 as a Keleut implementation. See
`doc/log/260829-1-plan.md` for the implementation plan.

The language specification lives in the parent `keleut` repository (this repository
is a git submodule of it):

- `../reference/sample.kel` — surface syntax and language design (the comments are the spec)
- `../reference/MiniLang.scala` — reference implementation of the type inferencer

# Building

1. Install opam and create a switch with OCaml >= 5.2.
2. `opam install dune menhir sedlex`
3. `dune build`
4. `dune runtest`

# Testing

Golden tests live under `test/`. After changing expected output, run
`dune promote` to update the golden files, and commit the update separately
from implementation changes.

`test/sample/sample.kel` is an unmodified copy of `../reference/sample.kel`;
its header comment records the source revision. To sync it, copy the file again
and update that revision note.

# Etymology

The name Diktor comes from a character in Robert A. Heinlein's novel,
_By His Bootstraps_, because Diktor's goal is to help bootstrap other implementations.
