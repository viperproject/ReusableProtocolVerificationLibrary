# A Generic Methodology for the Modular Verification of Security Protocol Implementations -- Reusable Verification Library

[![Reusable Verification Library](https://github.com/viperproject/ReusableProtocolVerificationLibrary/actions/workflows/library.yml/badge.svg?branch=main)](https://github.com/viperproject/ReusableProtocolVerificationLibrary/actions/workflows/library.yml?query=branch%3Amain)

This repository hosts the Reusable Verification Library as a Go module, which enables easy integration into Go projects.
This module simplifies verifying security properties for protocol implementations as described in the paper "A Generic Methodology for the Modular Verification of Security Protocol Implementations", published at ACM CCS '23 [[published version]](https://doi.org/10.1145/3576915.3623105) [[extended version]](https://arxiv.org/abs/2212.02626).
The entire artifact for this paper, which includes this verfication library, is available [here](https://github.com/viperproject/SecurityProtocolImplementations) and has been archived on Zenodo (DOI: [10.5281/zenodo.8330913](https://doi.org/10.5281/zenodo.8330913)). The paper can be cited as follows (for BibTeX):
```BibTex
@InProceedings{ArquintSchwerhoffMehtaMueller23,
  author = {Arquint, Linard and Schwerhoff, Malte and Mehta, Vaibhav and M\"uller, Peter},
  title = {A Generic Methodology for the Modular Verification of Security Protocol Implementations},
  year = {2023},
  isbn = {9798400700507},
  publisher = {Association for Computing Machinery},
  address = {New York, NY, USA},
  booktitle = {Proceedings of the 2023 ACM SIGSAC Conference on Computer and Communications Security},
  pages = {1377-1391},
  numpages = {15},
  keywords = {protocol implementation verification, symbolic security, separation logic, automated verification, injective agreement, forward secrecy},
  location = {Copenhagen, Denmark},
  series = {CCS '23},
  doi = {10.1145/3576915.3623105},
  url = {https://doi.org/10.1145/3576915.3623105},
  urltext = {Publisher},
  url1 = {https://pm.inf.ethz.ch/publications/ArquintSchwerhoffMehtaMueller23.pdf},
  url1text = {PDF},
  abstract = {Security protocols are essential building blocks of modern IT systems. Subtle flaws in their design or implementation may compromise the security of entire systems. It is, thus, important to prove the absence of such flaws through formal verification. Much existing work focuses on the verification of protocol *models*, which is not sufficient to show that their *implementations* are actually secure. Verification techniques for protocol implementations (e.g., via code generation or model extraction) typically impose severe restrictions on the used programming language and code design, which may lead to sub-optimal implementations. In this paper, we present a methodology for the modular verification of strong security properties directly on the level of the protocol implementations. Our methodology leverages state-of-the-art verification logics and tools to support a wide range of implementations and programming languages. We demonstrate its effectiveness by verifying memory safety and security of Go implementations of the Needham-Schroeder-Lowe, Diffie-Hellman key exchange, and WireGuard protocols, including forward secrecy and injective agreement for WireGuard. We also show that our methodology is agnostic to a particular language or program verifier with a prototype implementation for C.}
}
```

Maintainer: [Linard Arquint](https://linardarquint.com)
