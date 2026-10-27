# leanpep-single-performance-pg-v1

The format is a new explicit scalar-lifting layer above the unchanged D5 format.
Unknown fields, duplicate JSON keys, invalid dimensions/indices and inexact
number syntax are rejected. Numbers use {"num": integer, "den": positive integer}.

Required top-level fields:

- format: "leanpep-single-performance-pg-v1"
- layout: "tau_first_value_performance_first_row_v1"
- base_source: a D5 document WITHOUT its upper field. It contains D5's format,
  horizon, origin, source, ordering, row_rules and multiplier_convention.
- performance_rule: {sense: "geZero" or "leZero", scale: exact rational}
- extended_rows: the complete submitted raw row array, of length base_rows+1
- objective: submitted exact scalar/Gram expression in base_values+1 scalar slots
- upper: the sole submitted upper certificate, in the extended dimension

There is NO supplied base upper certificate. Internally, the Python implementation
uses a private zero-valued carrier to reuse D5's strict source parsing and data
rendering routines. That carrier is not in this schema, is never checked as the
user's proof, is removed before Lean rendering, and is never exported. The real
reduced upper is always the exact elimination of the submitted extended upper.

Rows and values have independent roles. Index 0 in the value vector is tau;
index 0 in the row vector is the performance inequality. Other value and row
indices are offset by one from their D5 SOURCE-STORAGE indices. Tau has no Gram
coordinate and no smooth/nonsmooth sample. The two original sample lists and
the original basis are in base_source and remain unchanged.

Let o be base_source.source.objective. Expected row 0 is the raw encoding of
scale*(embed(o)-tau)>=0 using performance_rule.sense. Expected row i+1 is the
scalar-slot lifting of base_source.source.constraints[i], with exactly the
original D5 raw sense and scale. The extended objective is tau, not o or -tau.
The complete extended rows/objective are checked before substituting tau=o.

upper.assumption_terms.index is relative to extended_rows. Multiple references
to row 0 are allowed. Their nonnegative oriented weights satisfy total
weight*performance_rule.scale=1 when the full raw certificate is accepted.
Retained indices are decremented by one BEFORE D5 multiplier scaling and D4
row-permutation inversion. Bounds, dual matrix and PSD factors are unchanged.

All original D5 multiplier sign, source binding, empty implicit interpolation,
ordering, origin and component-class guards remain mandatory.

## CLI

python3 tools/import_proximal_gradient_performance.py \
  data/fixtures/composite_performance/pg_three.json \
  --expected-steps 3 \
  --lean /tmp/PGPerformanceThree.lean \
  --report /tmp/PGPerformanceThree_report.json \
  --base-json /tmp/PGPerformanceThree_base.json \
  --namespace LeanPEP.Imported.PGPerformanceThree \
  --require-diagnostic-pass

--base-json is optional. Its result is a standard D5 artifact and can pass to
the unchanged D5, D4, D3 and D2 importers. Nonempty implicit interpolation is
rejected when requesting this export, even at zero weight.

Default: validly typed but mathematically failing inputs may be rendered as
untrusted data with failed diagnostics. --require-diagnostic-pass returns exit
code 2 for such failure. A Python pass is NOT Lean acceptance; reports explicitly
retain lean_checked=false, live_capture_performed=false and
provenance_authenticated=false. A reduced candidate's acceptance does not retroactively
certify the original lifted input; the full joint guard must still be used.

No auxiliary-order inference, extra-row inference, row repair, solver execution,
numeric tolerance or producer authentication occurs. All input/output paths
must be distinct. Normal regeneration does not generate expected source data.
