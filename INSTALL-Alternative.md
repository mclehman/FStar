## Online editor ##

The easiest way to try out F\* quickly is directly in your browser by using
the [online F\* editor] that's part of the [F\* tutorial].

[online F\* editor]: https://www.fstar-lang.org/run.php
[F\* tutorial]: https://www.fstar-lang.org/tutorial/


## Easy Install ##

### Homebrew formula for (MacOS) ###

On Macs you can build and install the latest F\* release using Homebrew.
This will install F\* and all required dependencies (including Z3):

        $ brew install fstar

Please read the Caveat displayed at the end of the installation if you
intend to extract code to OCaml, F\# or C.

### OPAM package (all platforms)###

**Note:** If you build F\* from sources you will also need to get a Z3
binary. This is further explained towards the end of this document.

If the OCaml package manager is present on your platform, you can
install the latest development version of F\* (`master` branch) and
required dependencies (except for Z3) using the following commands:

        $ opam pin add fstar --dev-repo
        $ opam install fstar

### Chocolatey Package (Windows) ###

On windows you can use chocolatey package manager to install and update fstar

    > choco install fstar

or

    > cinst fstar

you can find the package description [here](https://chocolatey.org/packages/FStar)

### Running F\* from a docker image ###

An alternative to installing binaries is to install a docker image.
We currently provide the following two on docker hub: `fstarlang/fstar-emacs`
with emacs support and `fstarlang/fstar` for purists.
The image is automatically kept up to date through a cloud build.

You only have to install docker and an X server for your platform and you are good to go.
See [Running F\* from a docker image](https://github.com/FStarLang/FStar/wiki/Running-F%2A-from-a-docker-image) for the details on how to use docker.


## Building F\* from sources ##

If you have a serious interest in F\* or want to report bugs then we
recommend that you build F\* from the sources on GitHub (the `master` branch).

### Prerequisite 1: Z3 SMT solver ###

To use F\* for verification, all the following ways to install need a Z3 binary.
Our binary packages include that already in `bin`, but if you compile
F\* from sources you need to get a Z3 binary yourself and add it to
your `PATH`. We recommend you use the Everest tested binaries here:
https://github.com/FStarLang/binaries/tree/master/z3-tested

### Prerequisite 2: Working OCaml setup  ###

Steps 2 and 3 below require a working OCaml setup. Any version of OCaml from 4.02.2 to 4.04.1 should do, but we recommend to F\* developers who plan to commit their extracted ML files to master to stick with 4.02.3, which is the latest OCaml version that works with opam on Windows.

#### Instructions for Windows ####

Please use the  [OCaml Installer for Windows](http://protz.github.io/ocaml-installer/).
Follow the [installation guide](https://github.com/protz/ocaml-installer/wiki)
that's over there (it's optimized for F\*). This will install both OCaml and OPAM.

#### Instructions for Linux and Mac OS X ####

0. Install OCaml
   - Can be installed using either your package manager or using OPAM
     (see below).

1. Install OPAM (version 1.2.x).

   - Installation instructions are available at various places
     (e.g., https://github.com/realworldocaml/book/wiki/Installation-Instructions#getting-opam
     or http://opam.ocaml.org/doc/Install.html).

#### Instructions for all OSes ####

2. Initialize and configure OPAM

   - You need to initialize it by running `opam init` and update the `PATH`
     variable to the `ocamlfind` and the OCaml libraries. If you allow
     `opam init` to edit your `~/.bashrc` or `~/.profile`, it is done
     automatically; otherwise, use: `eval $(opam config env)`.

   - If you're on Windows see https://github.com/protz/ocaml-installer/wiki
     for instructions on how to configure your environment for use with OPAM

3. Ensure that OPAM is using a recent enough version of OCaml

   - Type `opam switch list`. The current OCaml version used by opam
     is identified by the letter C. If it is not within the version
     range required by F\* (see above), type `opam switch ` and then
     the version number you wish to switch opam to.

4. F\* depends on a bunch of external OCaml packages which you should install using OPAM:

  ```sh
  $ opam install ocamlbuild ocamlfind batteries stdint zarith yojson fileutils pprint menhir ulex
  ```
  Some of the examples also require the `sqlite3` opam package, which depends
  on SQLite itself that you can install with `opam depext sqlite3` (at least on Linux)

  Please note that this list of packages is longer than the list in
  the [Testing a binary package](#testing-a-binary-package) section
  above, because the additional packages here are necessary to compile
  F\*.


### Building the F\* compiler itself ###

Once you have a working OCaml setup (see above)
just run the following command:

        $ make -C src/ocaml-output -j 6

The option `-j 6` controls the number of cores to be used in parallel build. This is a relatively standard unix feature.

**Note:** On Windows this generates a native F\* binary, that is, a binary that
does *not* depend on `cygwin1.dll`, since the installer above uses a
*native* Windows port of OCaml.  Cygwin is just there to provide `make` and
other utilities required for the build.
This also means that when linking C libraries with OCaml compiled objects one
needs to use the *correct* mingw libraries and *not* the Cygwin ones. OCaml uses
special `flexlink` technology for this. See `contrib/CoreCrypto/ml` and
`examples/crypto` for examples.

