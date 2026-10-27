# D8 approximate composite candidate format v1

Top-level exact keys:

  format: "leanpep-approximate-pg-sparse-v1"
  numeric_convention: "finite_decimal_strings_v1"
  source: a D7 exact artifact WITHOUT its upper field
  policy: {method: "limit_denominator", max_denominator: positive integer,
           max_abs_error: nonnegative finite decimal string}
  upper: {bound, objective, interp_terms, assumption_terms, dual_matrix}

`upper` mathematical numbers MUST be strings. Its scalar shape is identical to
the D7 upper, except that dual_factor is absent; exact factors are synthesized
from the submitted target matrix independently for each track. Indices are
unchanged bounded integers. Objective is a literal {const, value_coeff,
gram_coeff} record with all coefficients present. No default-zero fields.

The source remains in the exact num/den schema. Horizon, component samples,
coverage, row labels/rules, origin maps and storage permutations all follow D7.
No accepted exact certificate, symbolic known rate, or caller-supplied expected
acceptance Boolean is part of this input.

The policy bounds the reconstructed numerical inputs, not synthesized factor
weights or vectors and not frozen source rationals. Policy is reported/checked
independently of raw and reconstructed certificate feasibility. `report.json`
lists every scalar (including unchanged zeros), exact signed changes and all
three outcomes: raw accepted diagnostic, reconstructed exact accepted
diagnostic, reconstructed joint policy-and-certificate accepted diagnostic.

The Lean carrier uses a single SourceQ and two UpperCertQ values over exactly
that model. Generated code is data only except for finite-index bounds. The
separate regression file supplies decidable kernel checks. New Lean results
remain pending the user's build/smoke; Python reports never claim Lean success.

The four canonical examples live in data/fixtures/composite_candidates/. All are
clearly labeled deterministic regression fixtures, not PEPit capture.
