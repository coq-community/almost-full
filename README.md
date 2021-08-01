<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Almost Full

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]
[![DOI][doi-shield]][doi-link]

[docker-action-shield]: https://github.com/coq-community/almost-full/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/almost-full/actions?query=workflow:"Docker%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users


[doi-shield]: https://zenodo.org/badge/DOI/10.1007/978-3-642-32347-8_17.svg
[doi-link]: https://doi.org/10.1007/978-3-642-32347-8_17

Coq development of almost-full relations, including the Ramsey
Theorem, useful for proving termination.

## Meta

- Author(s):
  - Dimitrios Vytiniotis (initial)
  - Thierry Coquand (initial)
  - David Wahlstedt (initial)
- Coq-community maintainer(s):
  - Karl Palmskog ([**@palmskog**](https://github.com/palmskog))
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.10 or later
- Additional dependencies: none
- Coq namespace: `AlmostFull`
- Related publication(s):
  - [Stop When You Are Almost-Full](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.225.3021&amp;rep=rep1&amp;type=pdf) doi:[10.1007/978-3-642-32347-8_17](https://doi.org/10.1007/978-3-642-32347-8_17)

## Building instructions

``` shell
git clone https://github.com/coq-community/almost-full
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
