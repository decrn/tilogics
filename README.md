<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# 

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/decrn/em/workflows/Docker%20CI/badge.svg?branch=main
[docker-action-link]: https://github.com/decrn/em/actions?query=workflow:"Docker%20CI"






## Meta

- Author(s):
  - Steven Keuchel
  - Denis Carnier
- Additional dependencies:
  - 
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of 
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-decrn-em
```

To instead build and install manually, do:

``` shell
git clone https://github.com/decrn/em.git
cd em
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



