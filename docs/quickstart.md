# Quickstart

The recommended commands are in the root README. `OUT` is a reader-chosen absolute path outside the source; each named child must be new. No numerical solver is invoked by setup, verify, recover or tightness. Python 3.10+, Git, elan, network access to official Lean/GitHub/Mathlib sources and a supported C compiler are prerequisites for official setup. A matching binary cache avoids a dependency-source cold build. The recorded local machine has 32 GiB RAM; this is not a measured minimum.

On success, quick/pg2-verify/result.json contains `actual_upper_verified=true`, `selected_endpoint=structured`, and `bound=62500/499999`. Inspect Replay.lean and replay.log: the concrete namespace is `LeanPEP.Imported.Public.PG2`, including actual_upper and the printed standard axioms. The original consumer does not publish selected data after a failed Lean check.

For explicit offline verification after Core is built:

```sh
python3 tools/replay_pg_certificate.py verify \
  --source-root "$SOURCE" \
  --input "$SOURCE/data/cases/pg/two-step-reuse/capture.json" \
  --candidate "$SOURCE/data/cases/pg/two-step-reuse/selected_exact.json" \
  --output "$OUT/verify" --namespace LeanPEP.Imported.Public.PG2
```

Replace `verify` with `recover` and omit `--candidate` to execute the original 64-grid reconstruction. No solver or known-rate injection is part of recovery. The complete `full` entry actually runs this path and compares selected bytes with the accepted input. The two exact-pair demos are `tests/lean/regression/pg_one_tightness.lean` and `gd_one_tightness.lean`; `verify.py tightness` builds the required modules and executes both pairs and regressions.

Commands operate relative to the script's source root, independently of caller cwd. An external LEAN_PATH/PYTHONPATH is cleared. The fixed archive-specific commands remain restricted to their exact archived inputs; the general PG2 consumer still checks the supported source/profile instead of an archive whitelist.
