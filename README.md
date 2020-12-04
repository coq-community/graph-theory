# Graph Theory

[![CI][action-shield]][action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]
[![DOI][doi-shield]][doi-link]

[action-shield]: https://github.com/coq-community/graph-theory/workflows/CI/badge.svg?branch=master
[action-link]: https://github.com/coq-community/graph-theory/actions?query=workflow%3ACI

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users


[doi-shield]: https://zenodo.org/badge/DOI/10.1007/s10817-020-09543-2.svg
[doi-link]: https://doi.org/10.1007/s10817-020-09543-2

A library of formalized graph theory results, including various
standard results from the literature (e.g., Menger’s Theorem, Hall’s
Marriage Theorem, and the excluded minor characterization of
treewidth-two graphs) as well as some more recent results arising
from the study of relation algebra within the ERC CoVeCe project
(e.g., soundness and completeness of an axiomatization of graph
isomorphism).

## Meta

- Author(s):
  - Christian Doczkal (initial)
  - Damien Pous (initial)
  - Daniel Severín (external contributor)
- Coq-community maintainer(s):
  - Christian Doczkal ([**@chdoc**](https://github.com/chdoc))
  - Damien Pous ([**@damien-pous**](https://github.com/damien-pous))
- License: [CeCILL-B](LICENSE)
- Compatible Coq versions: 8.11 or later
- Additional dependencies:
  - MathComp's SSReflect library, version 1.10 or later
  - MathComp's finmap library
  - Hierarchy Builder
- Coq namespace: `GraphTheory`
- Related publication(s):
  - [Graph Theory in Coq - Minors, Treewidth, and Isomorphisms](https://hal.archives-ouvertes.fr/hal-02316859) doi:[10.1007/s10817-020-09543-2](https://doi.org/10.1007/s10817-020-09543-2)
  - [Completeness of an Axiomatization of Graph Isomorphism via Graph Rewriting in Coq](https://hal.archives-ouvertes.fr/hal-02333553) doi:[10.1145/3372885.3373831](https://doi.org/10.1145/3372885.3373831)
  - [A Formal Proof of the Minor-Exclusion Property for Treewidth-Two Graphs](https://hal.archives-ouvertes.fr/hal-01703922) doi:[10.1007/978-3-319-94821-8_11](https://doi.org/10.1007/978-3-319-94821-8_11)
  - [Formalization of the Domination Chain with Weighted Parameters (Short Paper)](https://drops.dagstuhl.de/opus/volltexte/2019/11091/) doi:[10.4230/LIPIcs.ITP.2019.36](https://doi.org/10.4230/LIPIcs.ITP.2019.36)

## Building and installation instructions

The easiest way to install the latest released version of Graph Theory
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-graph-theory
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/graph-theory.git
cd graph-theory
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Additional Documentation
Documentation describing the contents of the individual files is available on the [project website](https://perso.ens-lyon.fr/damien.pous/covece/graphs/)
