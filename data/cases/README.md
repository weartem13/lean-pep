# Concrete cases

| Case | Retained role | Selected normalized upper bound |
|---|---|---:|
| `pg/one-step-exact` | PG1 upper certificate and matched finite primal; actual tightness is proved by the library | 1/4 |
| `pg/two-step-original` | Original PG2 accepted structured certificate | 62497/499974 |
| `pg/two-step-reuse` | PG2 independent reuse input; recommended offline consumer example | 62500/499999 |
| `pg/three-step-original` | Accepted PG3 structured certificate | 41630/499559 |
| `gd/one-step-upper` | Earlier GD1 upper certificate | 83333/499997 |
| `gd/one-step-gap` | Earlier GD1 finite primal with a positive gap to its upper certificate | see retained primal audit |
| `gd/one-step-exact` | Later exact GD1 upper/finite-primal pair; actual tightness is proved by the library | 1/6 |
| `gd/two-step-original` | Accepted GD2 upper certificate | 50000/499999 |

Names identify roles rather than asserting that all instances are tight. The PG3 and GD2 cases retain their original evidence and are not supported by the fixed PG2 generic consumer CLI. Capture/selected/primal/Lean bytes and namespaces remain unchanged. The generated `Replay.lean`, `UpperReplay.lean`, and `PrimalReplay.lean` files are retained proof inputs, not caches.

The GD1 `replay-check/selected_primal.json` is the retained second identical output used by a determinism regression. PG1 `live-evidence/Replay.lean` preserves the earlier default capture's negative result; the accepted structured endpoint is `UpperReplay.lean`.

File-level identities and original case IDs are in [the evidence index](../paper/evidence-index.json). The current PG/GD tightness probes and negative regressions are under `tests/lean/regression/`; their library declarations retain the original fully qualified names.
