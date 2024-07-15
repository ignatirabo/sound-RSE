# Sound Symbolic Execution via Abstract Interpretation

In this software we implement several symbolic execution analyzers that are sound.
Also there is an implementation of dependence analysis from *Static Analysis of Information flow using Hypercollecting Semantics* [[1]](https://arxiv.org/abs/1608.01654).

## Installation

### Requirements

This project is implemented in OCaml 4.12.0, but any version should work. To install OCaml and OPAM you can check the following [link](https://opam.ocaml.org/doc/Install.html).

Also several opam libraries are required:
- `z3` is being used to check propositions,
- `bitv` is used to model security lattices,
- `dune` is the builder, and
- `apron` is a library for abstract domains.
These can be installed with `opam install z3 bitv dune apron`

### Build

The project is built using [dune](https://dune.build/):
- to build: `make`, equivalent to `dune build --root src main.exe`.
- to clean: `make clean`, equivalent to `dune --root src clean`.

The link to the executable can be found in the current directory.

It is important to notice that the compilation does not work with bytecode automatically, we need to define a environment path.

## Usage

Compiled program is `main.exe` and is used by activating switches and providing
a program to execute.

To execute the tests of the submission:
```
./main.exe --test
```

To execute different analyses of different programs:
```
./main.exe [ switches ] <file>
```

Switches for non-relational analysis are as follows:
- `--sse` activates sound symbolic execution.
- `--intvs` activates intervals domain.
- `--poly` activates convex polyhedra domain.

For relational analysis:
- `--rse` activates relational symbolic execution.
- `--dep` activates dependence analysis.

By combining the switches we can get the different combinations presented on the
submission.
We will list them:
1. `./main.exe --sse <file>` executes **SoundSE**.
2. `./main.exe --sse --intvs <file>` executes **RedSoundSE** with intervals.
2. `./main.exe --sse --poly <file>` executes **RedSoundSE** with polyhedra.
3. `./main.exe --rse <file>` executes **SoundRSE**.
4. `./main.exe --rse --dep <file>` executes **RedSoundRSE**.
5. `./main.exe --rse --dep --intvs` executes **RedSoundRSE** instantiated with
**RedSoundSE** with intervals.
5. `./main.exe --rse --dep --intvs` executes **RedSoundRSE** instantiated with
**RedSoundSE** with polyhedra.

## Folder structure

- `src/` contains all source OCaml files plus *dune* build files.
- `programs/` contains programs to analyze.
