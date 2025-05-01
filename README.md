
## Getting Started

### Prerequisites
* Install [OCaml](https://ocaml.org/docs/installing-ocaml)
* Install [Dune](https://dune.build/install)

### Build and run tests
```
dune build @default @runtest
```
or to continuously build and update test outputs
```
dune build @default @runtest --auto-promote --watch
```

### Format code
```
dune fmt
```
