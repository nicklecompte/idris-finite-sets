# idris-finite-sets

Tools for verified finite algebra / combinatorics in Idris. Currently this is
basically a port of [Firsov and Uustalu's Agda library](http://firsov.ee/finset/).
However, I plan to add tools around finite groups and counting problems.

This software is written in Literate Idris, and intended to be both a library
for Idris programs and a book for Idris programmers. For readers, familiarity
with basic dependently-typed programming as covered in [Type-Driven Development
with Idris](https://www.manning.com/books/type-driven-development-with-idris) is
assumed, along with a familiarity with the discrete mathematics commonly seen in
an undergraduate introduction to the topic. But we assume no deeper familiarity
with type theory or set theory.

## Disclaimer and notes on public domain release

The nice thing about Idris programs is that they generally do what they say on
the tin. That said, this program is full of holes (both literal and conceptual),
and should not be used for anything safety-or-career-critical.

The code and text here are released under [CC0](https://creativecommons.org/publicdomain/zero/1.0/legalcode), 
see `COPYING` for more information. The basic idea behind "copyright" of the 
code or commentary in this repository is that the set theoretic and algebraic
ideas used here are considerably older than I am, and that any "original" ideas
are much more a consequence of limitations in Idris and the author's own ability

That said, if you end up using this for anything serious, an acknowledgement 

## Bibliography and acknowledgments

- [Firsov and Uustalu, Dependently typed programming with finite sets](http://firsov.ee/finset/)
- [Agda's finite-prover](https://github.com/agda/agda-finite-prover)
- [Ligant-Ting Chen's Finite Sets in Cubical Agda](https://github.com/L-TChen/FiniteSets)