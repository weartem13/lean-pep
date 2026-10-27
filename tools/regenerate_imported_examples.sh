#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# v0.7 approximate input: preserve the raw decimal semantics, produce a
# separately reconstructed exact candidate, and record the complete hash/report
# chain before either candidate reaches Lean.
python3 tools/prepare_approx_bundle.py \
  data/fixtures/approximate/two_step_near_exact.json \
  --raw-exact data/fixtures/generated/two_step_near_exact_raw.json \
  --reconstructed-exact data/fixtures/generated/two_step_near_exact_reconstructed.json \
  --report data/fixtures/generated/two_step_near_exact_reconstruction_report.json \
  --manifest data/fixtures/generated/two_step_near_exact_comparison_manifest.json \
  --comparison-lean LeanPEP/Imported/TwoStepApproxComparison.lean \
  --raw-namespace LeanPEP.Imported.TwoStepApproxRaw \
  --reconstructed-namespace LeanPEP.Imported.TwoStepApproxReconstructed \
  --comparison-namespace LeanPEP.Imported.TwoStepApproxComparison

# The exact schema-v1 importer remains the sole JSON-to-Lean path for both
# approximate tracks.
python3 tools/import_exact_bundle.py \
  data/fixtures/generated/two_step_near_exact_raw.json \
  LeanPEP/Imported/TwoStepApproxRaw.lean \
  --namespace LeanPEP.Imported.TwoStepApproxRaw

python3 tools/import_exact_bundle.py \
  data/fixtures/generated/two_step_near_exact_reconstructed.json \
  LeanPEP/Imported/TwoStepApproxReconstructed.lean \
  --namespace LeanPEP.Imported.TwoStepApproxReconstructed

# Existing v0.6 exact examples remain regression inputs.
python3 tools/import_exact_bundle.py \
  data/fixtures/external/two_step_exact.json \
  LeanPEP/Imported/TwoStepExact.lean \
  --namespace LeanPEP.Imported.TwoStepExact

python3 tools/import_exact_bundle.py \
  data/fixtures/external/two_step_bad_metadata.json \
  LeanPEP/Imported/TwoStepBadMetadata.lean \
  --namespace LeanPEP.Imported.TwoStepBadMetadata

python3 tools/import_exact_bundle.py \
  data/fixtures/external/two_step_bad_primal.json \
  LeanPEP/Imported/TwoStepBadPrimal.lean \
  --namespace LeanPEP.Imported.TwoStepBadPrimal

python3 tools/import_exact_bundle.py \
  data/fixtures/external/two_step_bad_bound.json \
  LeanPEP/Imported/TwoStepBadBound.lean \
  --namespace LeanPEP.Imported.TwoStepBadBound

# v0.11A exact general-dimensional Gram bundles. The legacy scalar exact
# schema remains unchanged; this is a separate strict JSON boundary.
python3 tools/import_exact_gram_bundle.py \
  data/fixtures/gram_external/one_step_exact.json \
  LeanPEP/Imported/GramOneStepExact.lean \
  --namespace LeanPEP.Imported.GramOneStepExact

python3 tools/import_exact_gram_bundle.py \
  data/fixtures/gram_external/one_step_bad_metadata.json \
  LeanPEP/Imported/GramOneStepBadMetadata.lean \
  --namespace LeanPEP.Imported.GramOneStepBadMetadata

python3 tools/import_exact_gram_bundle.py \
  data/fixtures/gram_external/one_step_bad_primal.json \
  LeanPEP/Imported/GramOneStepBadPrimal.lean \
  --namespace LeanPEP.Imported.GramOneStepBadPrimal

python3 tools/import_exact_gram_bundle.py \
  data/fixtures/gram_external/one_step_bad_primal_factor.json \
  LeanPEP/Imported/GramOneStepBadPrimalFactor.lean \
  --namespace LeanPEP.Imported.GramOneStepBadPrimalFactor

python3 tools/import_exact_gram_bundle.py \
  data/fixtures/gram_external/one_step_bad_upper.json \
  LeanPEP/Imported/GramOneStepBadUpper.lean \
  --namespace LeanPEP.Imported.GramOneStepBadUpper

# v0.11B approximate general-dimensional Gram input. Every mathematical
# scalar remains a finite decimal string until the untrusted preprocessor emits
# two unchanged external-gram-format-v1 bundles with distinct semantics.
python3 tools/prepare_approx_gram_bundle.py \
  data/fixtures/gram_approximate/one_step_near_exact.json \
  --raw-exact data/fixtures/gram_generated/one_step_near_exact_raw.json \
  --reconstructed-exact data/fixtures/gram_generated/one_step_near_exact_reconstructed.json \
  --report data/fixtures/gram_generated/one_step_near_exact_reconstruction_report.json \
  --manifest data/fixtures/gram_generated/one_step_near_exact_comparison_manifest.json \
  --comparison-lean LeanPEP/Imported/GramOneStepApproxComparison.lean \
  --raw-namespace LeanPEP.Imported.GramOneStepApproxRaw \
  --reconstructed-namespace LeanPEP.Imported.GramOneStepApproxReconstructed \
  --comparison-namespace LeanPEP.Imported.GramOneStepApproxComparison

# Both approximate Gram tracks reuse the exact Gram importer unchanged.
python3 tools/import_exact_gram_bundle.py \
  data/fixtures/gram_generated/one_step_near_exact_raw.json \
  LeanPEP/Imported/GramOneStepApproxRaw.lean \
  --namespace LeanPEP.Imported.GramOneStepApproxRaw

python3 tools/import_exact_gram_bundle.py \
  data/fixtures/gram_generated/one_step_near_exact_reconstructed.json \
  LeanPEP/Imported/GramOneStepApproxReconstructed.lean \
  --namespace LeanPEP.Imported.GramOneStepApproxReconstructed

# v0.11C concrete PEPit one-step adapter.  The committed source artifact is a
# deterministic PEPit-shaped regression fixture, not a claim that PEPit or a
# solver was executed during regeneration.  The optional live exporter can emit the same
# source schema in an environment with the pinned PEPit revision and solver.
python3 tools/adapt_pepit_one_step.py \
  data/fixtures/pepit/one_step_gd_solver_artifact.json \
  --approximate-gram data/fixtures/pepit_generated/one_step_gd_approximate_gram.json \
  --report data/fixtures/pepit_generated/one_step_gd_adapter_report.json \
  --manifest data/fixtures/pepit_generated/one_step_gd_adapter_manifest.json \
  --lean-metadata LeanPEP/Imported/PEPitOneStepAdapter.lean \
  --lean-namespace LeanPEP.Imported.PEPitOneStepAdapter \
  --comparison-import LeanPEP.Imported.PEPitOneStepApproxComparison

# The adapted numerical payload reuses the verified v0.11B dual-track path.
python3 tools/prepare_approx_gram_bundle.py \
  data/fixtures/pepit_generated/one_step_gd_approximate_gram.json \
  --raw-exact data/fixtures/pepit_generated/one_step_gd_raw.json \
  --reconstructed-exact data/fixtures/pepit_generated/one_step_gd_reconstructed.json \
  --report data/fixtures/pepit_generated/one_step_gd_reconstruction_report.json \
  --manifest data/fixtures/pepit_generated/one_step_gd_comparison_manifest.json \
  --comparison-lean LeanPEP/Imported/PEPitOneStepApproxComparison.lean \
  --raw-namespace LeanPEP.Imported.PEPitOneStepApproxRaw \
  --reconstructed-namespace LeanPEP.Imported.PEPitOneStepApproxReconstructed \
  --comparison-namespace LeanPEP.Imported.PEPitOneStepApproxComparison

python3 tools/import_exact_gram_bundle.py \
  data/fixtures/pepit_generated/one_step_gd_raw.json \
  LeanPEP/Imported/PEPitOneStepApproxRaw.lean \
  --namespace LeanPEP.Imported.PEPitOneStepApproxRaw

python3 tools/import_exact_gram_bundle.py \
  data/fixtures/pepit_generated/one_step_gd_reconstructed.json \
  LeanPEP/Imported/PEPitOneStepApproxReconstructed.lean \
  --namespace LeanPEP.Imported.PEPitOneStepApproxReconstructed

# A formulation-order regression uses the same mathematical candidate but
# swaps two PEPit interpolation constraints.  Lean rejects the source profile
# independently of the raw/reconstructed numerical outcomes.
python3 tools/adapt_pepit_one_step.py \
  data/fixtures/pepit/one_step_gd_bad_constraint_order.json \
  --approximate-gram data/fixtures/pepit_generated/one_step_gd_bad_constraint_order_approximate_gram.json \
  --report data/fixtures/pepit_generated/one_step_gd_bad_constraint_order_adapter_report.json \
  --manifest data/fixtures/pepit_generated/one_step_gd_bad_constraint_order_adapter_manifest.json \
  --lean-metadata LeanPEP/Imported/PEPitOneStepBadConstraintOrderAdapter.lean \
  --lean-namespace LeanPEP.Imported.PEPitOneStepBadConstraintOrderAdapter \
  --comparison-import LeanPEP.Imported.PEPitOneStepApproxComparison

# Typed-symbolic provenance regression: the declared fingerprint and all
# lightweight metadata remain canonical, but one PEPit-native interpolation
# coefficient is altered.  The adapted mathematical payload is unchanged;
# Lean's typed source-formulation audit must reject the source independently.
python3 tools/adapt_pepit_one_step.py \
  data/fixtures/pepit/one_step_gd_bad_symbolic_coefficient.json \
  --approximate-gram data/fixtures/pepit_generated/one_step_gd_bad_symbolic_coefficient_approximate_gram.json \
  --report data/fixtures/pepit_generated/one_step_gd_bad_symbolic_coefficient_adapter_report.json \
  --manifest data/fixtures/pepit_generated/one_step_gd_bad_symbolic_coefficient_adapter_manifest.json \
  --lean-metadata LeanPEP/Imported/PEPitOneStepBadSymbolicCoefficientAdapter.lean \
  --lean-namespace LeanPEP.Imported.PEPitOneStepBadSymbolicCoefficientAdapter \
  --comparison-import LeanPEP.Imported.PEPitOneStepApproxComparison

# v0.13D1 exact matrix synthesis. No solver or floating-point reconstruction.
python3 tools/regenerate_psd_synthesis.py

# v0.13D2 centered exact composite snapshots (NOT live PEPit capture).
python3 tools/regenerate_proximal_gradient_source.py

# v0.13D3 fixed uncentered exact coordinates (NOT live capture).
python3 tools/regenerate_proximal_gradient_coordinates.py

# v0.13D4 exact storage permutations before D3 origin elimination (NOT live capture).
python3 tools/regenerate_proximal_gradient_ordering.py

# v0.13D5 exact signed/positively scaled source rows (NOT live capture).
python3 tools/regenerate_proximal_gradient_rows.py

# v0.13D6 exact single-performance scalar lifting (NOT live capture).
python3 tools/regenerate_proximal_gradient_performance.py

# v0.13D7 checked omissions of coefficientwise zero rows (NOT live capture).
python3 tools/regenerate_proximal_gradient_sparse.py

# v0.13D8 frozen exact source, raw/reconstructed numerical candidates (NOT live capture).
python3 tools/regenerate_proximal_gradient_candidates.py

# v0.13D9 OFFLINE capture-protocol fixtures, never a solver call.
python3 tools/regenerate_pepit_proximal_gradient_capture.py

# D10: offline fixed-residual completion; never runs PEPit or a solver.
python3 tools/regenerate_pepit_proximal_gradient_completion.py

# D11: exact budget/nonnegativity feasibility; offline simulations only.
python3 tools/regenerate_bounded_pepit_capture.py
