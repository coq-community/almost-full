# Almost Full

[![Travis][travis-shield]][travis-link]

[travis-shield]: https://travis-ci.com/palmskog/almost-full.svg?branch=master
[travis-link]: https://travis-ci.com/palmskog/almost-full/builds




Coq development of almost-full relations, including the Ramsey
Theorem, useful for proving termination.

## Meta

- Author(s):
  - Dimitrios Vytiniotis (initial)
  - Thierry Coquand (initial)
  - David Wahlstedt (initial)
- License: [Unknown](LICENSE)
- Compatible Coq versions: 8.9 or later
- Additional dependencies: none
- Coq namespace: `AlmostFull`
- Related publication(s):
  - [Stop When You Are Almost-Full](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.225.3021&amp;rep=rep1&amp;type=pdf) doi:[10.1007/978-3-642-32347-8_17](https://doi.org/10.1007/978-3-642-32347-8_17)

## Building instructions

``` shell
git clone https://github.com/palmskog/almost-full
cd almost-full
make   # or make -j <number-of-cores-on-your-machine>
```

## Documentation

Included files:
- `AlmostFull.v`: Basic setup, connections to well-founded relations
- `AFConstructions.v`: Almost-full relation constructions and type-based combinators
- `AlmostFullInduction.v`: Various induction principles 
- `AFExamples.v`: Examples
- `Terminator.v`: Deriving the Terminator proof rule
