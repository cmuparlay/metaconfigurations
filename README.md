# Setup and Installation

To build, you will need [opam](https://opam.ocaml.org/doc/Install.html) installed. Then, create a new switch
as follows:

```
opam switch create metaconfig 5.2.0
```

Then, install the necessary dependencies:

```
opam switch metaconfig
opam repo add coq-released https://coq.inria.fr/opam/released
opam install . --deps-only
```

Now, you can build the project:

```
opam exec -- dune build
```

Compilation ensures all proofs are complete.
The `Print Assumptions` command demonstrates
that only functional extensionality is
axiomatized.

## Directory Structure

The project is organized as follows:

```
metaconfig/
├── src/
    ├── theories/
        ├── Dynamics
        │   ├── Procedure.v
        │   ├── Stmt.v
        │   ├── Term.v
        ├── Syntax
        │   ├── Stmt.v
        │   ├── Term.v
        │   ├── Value.v
        ├── Map.v
        ├── Object.v
```

The `theories/Syntax` directories contains syntactic definitions for most constructs. `theories/Dynamics`
contains the semantics. `theories/Dynamics/Procedure.v`
contains most of the main theorems. In this file, `FullTracker.adequacy` corresponds to lemma 1 (Adequacy) in the paper. `RWCAS.linearizable` corresponds to the proof
of linearizability for the concurrent register.
