# leanpep-permuted-pg-source-v1

This exact input format adds `ordering` to D3's uncentered snapshot format.
Other top-level fields are `format`, `horizon`, `origin`, `source`, and `upper`.
Unknown fields and duplicate JSON keys are rejected. Rational numbers are exact
objects {"num": integer, "den": positive integer}; floats, decimal strings and
zero denominators are not accepted. The original importer remains unchanged.

`ordering` has exactly five keys: basis, values, smooth, nonsmooth, rows.
Each contains two zero-based integer arrays of the corresponding exact size:

    {"to_source": [1, 2, 0], "to_canonical": [2, 0, 1]}

This example means canonical slot 0 lives at source slot 1, canonical 1 at
source 2, canonical 2 at source 0. It is deliberately not self-inverse.

Source coefficient arrays and their labels are gathered with `to_source`.
Every embedded reference (sample.value_index, upper assumption index, implicit
term i/j) is mapped using `to_canonical`. Gram/dual matrices are gathered on
BOTH axes, factor vectors on their one basis axis. All term weights and the
bound stay exactly unchanged. No factor synthesis occurs during import.

Sample storage permutations are separate within the smooth and nonsmooth
component. RowTag i/j remain LOGICAL component point IDs, NOT storage offsets;
constraint_order is moved with constraints but i/j themselves are not changed.
The centered axis of the rectangular center_matrix/section_matrix stays fixed.

The source header still contains all the D3 fields. Its basis_order,
value_order and constraint_order describe source storage. Its coordinates
string designates D3's canonical family, not a requirement to store in that
order before D4 restores it. Wrong labels or metadata cannot be fixed by
copying expected labels over them; all are submitted to Lean.

The parser checks dimensions and range bounds. In-range non-inverse maps are
emitted as candidates for Lean rejection, never repaired. With such malformed
maps the intermediate old-format JSON may itself violate a legacy parser
condition (for example, duplicate labels); the diagnostic records that error
and rejects the candidate. Neither a diagnostic failure nor a rejected factor
is a proof that the optimization theorem is false.

## Example

    python3 tools/import_proximal_gradient_ordering.py \
      data/fixtures/composite_ordering/pg_three.json \
      --expected-steps 3 \
      --lean /tmp/PGOrderThree.lean \
      --report /tmp/PGOrderThree_report.json \
      --native-json /tmp/PGOrderThree_native.json \
      --namespace LeanPEP.Imported.PGOrderThree

The optional native-json output is deterministic transport of the candidate,
not a repair or an acceptance theorem. Valid inputs can then be passed through
the unchanged D3 importer, and its centered output through unchanged D2.
`--require-diagnostic-pass` returns 2 when exact Python checks fail, while
retaining emitted candidate/diagnostic files for inspection. Lean checks must
still be run separately. All input and output paths must be distinct.

## Trust boundary

Origin and hashes are provenance records, not mathematical acceptance conditions
or producer authentication. The Lean theorem concerns the generated typed
payload, not source-byte authenticity. `origin.mode` is either
`deterministic_regression_fixture` or `external_exact_snapshot`; the committed
examples use the former. No live capture is performed or inferred.
