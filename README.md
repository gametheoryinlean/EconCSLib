# EconCSLib

EconCSLib is a Lean 4 library and cross-linked knowledge base for
computational economics, built on
[Mathlib](https://github.com/leanprover-community/mathlib4).

The initial public release focuses on reusable foundations rather than complete
coverage of the field. It includes strategic, extensive, and coalitional games;
social choice and fair division; matching; auctions and mechanism design;
utility theory; and supporting mathematics such as fixed-point, minimax, and
linear-programming results.

| Surface | Link |
|---------|------|
| API reference | <https://gametheoryinlean.github.io/econcslib_doc/> |
| Knowledge blueprint | <https://gametheoryinlean.github.io/blueprint/> |

The blueprint records both formalized material and mathematical targets that
still need Lean implementations. The stable Lean import surface contains no
deferred proofs.

## Getting Started

```bash
git clone https://github.com/gametheoryinlean/EconCSLib.git
cd EconCSLib
lake exe cache get
lake build
lake build EconCSLib.Examples
```

**Lean version:** `leanprover/lean4:v4.30.0`

Import the stable library surface with:

```lean
import EconCSLib
```

Worked examples live under [`EconCSLib/Examples/`](EconCSLib/Examples).
Experimental open-problem interfaces under
[`EconCSLib/OpenProblem/`](EconCSLib/OpenProblem) are opt-in.

## Documentation

- [`docs/design.md`](docs/design.md) describes architecture and contribution
  rules.
- [`docs/design/`](docs/design) contains focused API notes.
- [`docs/research/`](docs/research) retains selected mathematical design and
  proof-strategy notes.
- [`docs/maintainers/`](docs/maintainers) documents reproducible publishing
  workflows.
- [`docs/knowledge/`](docs/knowledge) is the editable source for the generated
  knowledge blueprint.
- [`AGENTS.md`](AGENTS.md) is supplemental guidance for coding agents.

## Contributing

Contributions are welcome. See [`CONTRIBUTING.md`](CONTRIBUTING.md), then browse
the [issue tracker](https://github.com/gametheoryinlean/EconCSLib/issues) or
start a [discussion](https://github.com/gametheoryinlean/EconCSLib/discussions).

## AI Assistance

AI tools have assisted with routine proof engineering, maintenance, and
documentation. Domain contributors remain responsible for reviewing
mathematical models, theorem statements, and public API decisions.

## History

EconCSLib grew out of a game-theory formalization project at Xiamen University
Malaysia. See [`docs/HISTORY.md`](docs/HISTORY.md) for a concise project
history.

## Contributors

Coordinators (alphabetical by surname): [Bei Xiaohui](https://github.com/xbei)
(NTU), Fu Hongfei, [Ma Jiajun](https://github.com/jiajunma) (XMUM),
[Zhan JING](https://github.com/zhanquen) (SJTU).

Contributors: [Wang Haocheng](https://github.com/hcWang942),
[Lü Yuwei (吕宇维)](https://github.com/lyw-ops),
[Xing2222](https://github.com/Xing2222),
[Li Kai](https://github.com/Li-ba-by),
[Oh Siew Zher](https://github.com/Szher111),
[Ma Yuxuan](https://github.com/ma-yuxuan),
[Luo Yiding](https://github.com/matlyd),
[Timothy Wan](https://github.com/saddle196883) (NUS),
[ARTHURCHOU](https://github.com/ARTHURCHOU),
[abc12321](https://github.com/abc12321),
[Hennessy](https://github.com/Hennessyyyyy),
[XGCC666](https://github.com/XGCC666),
[Zli-Math](https://github.com/Zli-Math).

## References

- Maschler, Solan, Zamir, *Game Theory* (Cambridge University Press, 2013)
- Nisan, Roughgarden, Tardos, Vazirani, *Algorithmic Game Theory* (Cambridge
  University Press, 2007)
- Laraki, Renault, Sorin, *Mathematical Foundations of Game Theory* (Springer,
  2019)
- Krishna, *Auction Theory*, 2nd ed. (Academic Press, 2009)
