# Archive and migration index

The code root separates library, tools, tests, fixtures/cases and current documentation. The independent manuscript is retained in the author workspace and excluded from code exports. Seventy-three original smoke filenames live in tests/lean/smoke. Python tests live in tests/python. examples is reserved for small readable entry examples; its old fixture collection moved intact to data/fixtures. Required numbered PG/GD runs were mapped to data/cases without combining their gap/exact values.

The original working-tree snapshot (including .git), old frozen source packages/manifests, raw logs, all earlier drafts, internal reviewer/status materials and obsolete release runners are held in a private external archive. They are not runtime dependencies of this tree. A complete migration/compatibility table accompanies the preparation report; `data/paper/evidence-index.json` provides the public evidence subset and original/derived hashes.

Technical reference notes remain under docs/reference; their historical version labels describe prior milestones. The current README, quickstart and scripts/verification.json are the active maintenance entry. The historical release_gate.sh and validate_v014_snapshot.py are archived, not deleted or treated as the new authority.

The exporter copies no Git history. A first public checkout starts with a separate root commit; later releases retain that public history as described in [releasing.md](releasing.md). The content scan says nothing about old private Git refs, which are not publication inputs. No license grant or Git authorship is inferred from directory cleanup or the paper byline.
