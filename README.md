<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Graph Theory

[![Docker CI][docker-action-shield]][docker-action-link]
[![Chat][chat-shield]][chat-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]
[![DOI][doi-shield]][doi-link]

[docker-action-shield]: https://github.com/coq-community/graph-theory/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/graph-theory/actions/workflows/docker-action.yml
[chat-shield]: https://img.shields.io/badge/Zulip-join_chat-brightgreen.svg
[chat-link]: https://coq.zulipchat.com/#narrow/stream/284683-GraphTheory

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users


[doi-shield]: https://zenodo.org/badge/DOI/10.1007/s10817-020-09543-2.svg
[doi-link]: https://doi.org/10.1007/s10817-020-09543-2

A library of formalized graph theory results, including various
standard results from the literature (e.g., Menger's Theorem, Hall's
Marriage Theorem, the excluded minor characterization of
treewidth-two graphs, and Wagner's Theorem) as well as some more
recent results arising from the study of relation algebra within
the ERC CoVeCe project (e.g., soundness and completeness of an
axiomatization of graph isomorphism).

## Meta

- Author(s):
  - Christian Doczkal (initial)
  - Damien Pous (initial)
  - Daniel Severín (external contributor)
- Coq-community maintainer(s):
  - Christian Doczkal ([**@chdoc**](https://github.com/chdoc))
  - Damien Pous ([**@damien-pous**](https://github.com/damien-pous))
- License: [CeCILL-B](LICENSE)
- Compatible Coq versions: 8.18 or later
- Additional dependencies:
  - MathComp's [SSReflect library](https://math-comp.github.io), version 2.0 or later
  - MathComp's [Algebra library](https://math-comp.github.io)
  - MathComp's [finmap library](https://github.com/math-comp/finmap)
  - [Hierarchy Builder](https://github.com/math-comp/hierarchy-builder), version 1.5.0 or later
  - Gonthier's [formal proof](https://github.com/coq-community/fourcolor) of the Four-Color Theorem (optional dependency)
- Coq namespace: `GraphTheory`
- Related publication(s):
  - [A Variant of Wagner's Theorem Based on Combinatorial Hypermaps](https://hal.inria.fr/hal-03142192) doi:[10.4230/LIPIcs.ITP.2021.17](https://doi.org/10.4230/LIPIcs.ITP.2021.17)
  - [Graph Theory in Coq - Minors, Treewidth, and Isomorphisms](https://hal.archives-ouvertes.fr/hal-02316859) doi:[10.1007/s10817-020-09543-2](https://doi.org/10.1007/s10817-020-09543-2)
  - [Completeness of an Axiomatization of Graph Isomorphism via Graph Rewriting in Coq](https://hal.archives-ouvertes.fr/hal-02333553) doi:[10.1145/3372885.3373831](https://doi.org/10.1145/3372885.3373831)
  - [A Formal Proof of the Minor-Exclusion Property for Treewidth-Two Graphs](https://hal.archives-ouvertes.fr/hal-01703922) doi:[10.1007/978-3-319-94821-8_11](https://doi.org/10.1007/978-3-319-94821-8_11)
  - [Formalization of the Domination Chain with Weighted Parameters (Short Paper)](https://drops.dagstuhl.de/opus/volltexte/2019/11091/) doi:[10.4230/LIPIcs.ITP.2019.36](https://doi.org/10.4230/LIPIcs.ITP.2019.36)

## Building and installation instructions

To manually build and install the whole project, including Wagner's theorem which requires
the Coq proof of the Four-Color Theorem, do:

``` shell
git clone https://github.com/coq-community/graph-theory.git
cd graph-theory
make   # or make -j <number-of-cores-on-your-machine> 
make install
```

However, the easiest way to install released versions of Graph Theory
libraries selectively is via [opam](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-graph-theory # core library
opam install coq-graph-theory-planar # planarity results depending on coq-fourcolor
```

## Documentation

This project contains:

- a general purpose Coq library about graph theory:
  - directed graphs, simple graphs, multigraphs
  - paths, trees, forests, isomorphism, connected components, etc.
  - minors and tree decompositions
  - Menger's theorem and some of its corollaries (Hall's marriage theorem and König's theorem)
  - the excluded-minor characterisation of treewidth at most two graphs (as those excluding K4 as a minor)
- soundness and completeness of an axiomatization of isomorphism of two-pointed treewidth-two (`2p`) multigraphs:
  - isomorphisms up to label-equivalence and edge-flipping for multigraphs
  - 2p graphs form a 2p algebra and thus also a 2pdom algebra
  - every K4-free graph can be represented by a 2p-term
  - 2pdom axioms are complete w.r.t. graph isomorphism for connected 2p graphs.
- a proof of Wagner's theorem (planarity of K5 and K3,3 graphs) based on combinatorial hypermaps
- two proofs of the weak perfect graph theorem (WPGT):
  - one proof based on Lovasz's replication lemma
  - one proof based on a matrix rank argument

Additional information on the contents of individual files is available at the [project website](https://perso.ens-lyon.fr/damien.pous/covece/graphs/).
