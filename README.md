# dL

This repository contains an implemention of differential dynamic logic ([[http://symbolaris.com/logic/dL.html]]) in Coq. There are currently two files:

- theories/Logics.v : This formalizes the logics found in dL, in particular predicates over states (dL formulas), state relations (hybrid programs), and flow predicates (differential in-equations describing physical evolutions).
- theories/dL.v : This formalizes the operators of dL (e.g. assignment) in terms of the logics in Logics.v. This file also states and proves the proof rules of dL as Coq theorems. Finally, there is a small example at the end of the file to illustrate how verification works in this framework.

## Building the code

This project has several dependencies, and the best way to install both Coq and these dependencies is via opam. Instructions for getting started with opam reside here: [[http://coq.io/opam/get_started.html]]. Once you've installed the latest version of Coq (via opam), you'll need to install the following Coq packages:

- coq-charge-core
- coq-ext-lib

This will be sufficient to build most of the code. In order to complete the entire proof in the example, you'll need to install the semi-definite programming solver csdp, which is used for solving some arithmetic proof obligations. On Ubuntu systems, you can install it using

    apt-get install coinor-csdp

Once you've installed these dependencies, running ```make``` in the root directory should build both files.

## Working with the code

As an IDE for Coq, we use proof general: https://github.com/ProofGeneral/PG. It works well with the _CoqProject file in the root directory of this repository.
