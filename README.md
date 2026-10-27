# Lean-PEP

Lean-PEP consumes exact performance-estimation certificates and proves bounds for optimization algorithms in Lean. A parameterized semantic interface connects a checked proximal-gradient source and finite certificate to a function-level theorem; a capture interface additionally checks trace, raw-data and reconstruction-policy bindings.

The library includes PG/GD finite and actual-function results, arbitrary positive-horizon mathematics, exact one-step pairs, and explicit representation transports. The executable offline recovery/verification consumer supports its documented **PG2** profile. Its supplied certificate proves

`f(x 2) + h(x 2) - (f(xStar) + h(xStar)) ≤ (L:ℝ) * R² * (62500/499999)`.

The hypotheses are a complete real inner-product space, analytic smooth-convex `f` with gradient `g`, real-valued convex `h`, `L>0`, `R≥0`, a composite global minimizer, a two-step proximal-gradient run with step `1/L`, and initial squared distance at most `R²`. No separate stationarity or subgradient of `h` at `x0` is assumed.

## Start here

Install Python 3.10+, Git and elan; keep `lean-toolchain` and `lake-manifest.json` unchanged. Offline consumption uses Python's standard library. From a fresh extracted candidate, choose an **external**, unused output directory:

```sh
OUT="$(mktemp -d)"
python3 scripts/setup.py --output "$OUT/setup" --dependencies-only
python3 scripts/verify.py quick --output "$OUT/quick"
```

Setup fetches the nine pinned official dependencies and matching binary cache, then quick builds Core and actually verifies the supplied PG2 certificate. A matching clean external cache may instead be supplied with `setup.py --cache "$CACHE"`. The source manifest and 57-module content guard are checked; no author checkout, old ZIP or project objects are inputs.

For the complete maintenance checks, use an environment containing `requirements-test.txt`:

```sh
python3 scripts/verify.py full --output "$OUT/full"
python3 scripts/verify.py tightness --output "$OUT/tightness"
python3 scripts/clean.py
```

`verify.py MODE --list` prints the exact plan. Full includes all Python tests, deterministic generation checks, staged complete-library builds, all 73 smokes, independent regressions/Replays and an offline PG2 recovery. Tightness displays the PG/GD one-step exact-pair declarations and axioms. Clean defaults to a dry-run; `--apply` only removes its explicit rebuildable output list.

## Evidence and scope

The [declaration and execution map](docs/evidence/claim-evidence.md) connects the library's interfaces and accepted cases to their exact source and execution evidence. [Research data](data/paper/README.md) contains all eight fixed configurations, eight captures and seven distinct accepted payloads, including failed grid trials and duplicate relationships. Those experiments retain their original frozen source identity; later layout validation is recorded separately. [Cases](data/cases/README.md) distinguish gap and exact witnesses.

This code snapshot includes the implementation, tests, reproduction inputs and supporting evidence. The manuscript, PDF, typesetting resources, paper packages and internal editing records are maintained separately. `SOURCE_MANIFEST.json` and `PUBLIC_MANIFEST.json` identify the exported code and evidence bytes; record them together with the commit when reproducing a result.

The [Lean-PEP repository](https://github.com/weartem13/lean-pep) remains **private**. The selected software version is **0.1.0**; no tag or Release is asserted. The classical PG/GD bounds serve as validation cases, and the executable recovery/verification consumer uses the documented PG2 profile.

## Citation and licensing

[CITATION.cff](CITATION.cff) provides the repository, software version and bibliographic metadata for the accompanying unpublished manuscript, *Lean-PEP: Performance-Estimation Certificates to Formally Verified Algorithmic Bounds*, by Xinyuan Guo and Andersen Ang. DOI and arXiv identifiers are omitted until assigned.

Project-owned software, including the Lean proof sources and Python tools, is licensed under the **Apache License 2.0** (SPDX: `Apache-2.0`); see [LICENSE](LICENSE) for the official full text.

The separately maintained paper uses **CC-BY-4.0**. The migrated declaration/evidence maps retain that license under the limited scope stated in [docs/evidence/README.md](docs/evidence/README.md), with the full text in [docs/evidence/LICENSE](docs/evidence/LICENSE). These terms do not offer a choice of licenses for the whole repository or change the linked research data's existing status.

Existing third-party licenses and attribution notices remain applicable. External dependencies are fetched separately using the pinned lockfile and retain their own terms. The software license is the unmodified standard text, without an additional project copyright notice. The repository remains private, with no public Release or arXiv submission yet.

## Milestone releases

The [release procedure](docs/releasing.md) exports this maintained tree into a fresh directory. The first public repository starts with a new root commit; later milestone releases append commits to that same public history. Daily development is not automatically synchronized. See the [changelog](CHANGELOG.md).

- [Quickstart](docs/quickstart.md): prerequisites, expected output and direct consumer flags.
- [Architecture](docs/architecture.md): semantics and import boundary.
- [Reproducibility](docs/reproducibility.md): source/evidence identities and fresh-root validation.
- [Theorem index](docs/theorem-index.md): exact declarations and mathematical scope.
- [Development](docs/development.md): tests, generation, output and cleaning rules.
- [Archive index](docs/archive-index.md): migration and preserved historical evidence.
