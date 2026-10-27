import LeanPEP.Adapters.ProximalGradientCapture
import LeanPEP.GramPEP.ExternalBundle

/-! PG1 finite primal data only. Reuses the original PSD and explicit-assumption
checks, without imposing single-function interpolation on the composite carrier.
The native numerical policy is separate from the older dual policy. -/
namespace LeanPEP.Adapters.PGOnePrimal
open LeanPEP.GramPEP
open scoped BigOperators

structure NativeQ where
  gram : Gram 6 ℚ
  values : Fin 6 → ℚ

def NativeQ.data (d : NativeQ) : DataQ (Fin 6) 6 :=
  { gram := d.gram, value := d.values, position := fun _ => 0, gradient := fun _ => 0 }

def nativeModel (t : ProximalGradientCapture.TraceQ 0 10) : ModelQ 6 6 :=
  { position := fun _ => 0, gradient := fun _ => 0
    assumptions := List.ofFn fun i => LinearExprQ.scale (-1) (t.rows i) }

def coefficientOK (raw candidate : ℚ) : Bool :=
  decide (candidate.den ≤ 1000000 ∧ |candidate - raw| ≤ (1 / 1000000 : ℚ))

/-- All 36 matrix entries, followed by all six values; no factor entries. -/
def policy (raw candidate : NativeQ) : Bool :=
  (gramIndexPairs 6).all (fun ij => coefficientOK (raw.gram ij.1 ij.2)
    (candidate.gram ij.1 ij.2)) &&
  (List.finRange 6).all (fun i => coefficientOK (raw.values i) (candidate.values i))

def canonicalData (s : ProximalGradientSparse.SourceQ 0 10) (d : NativeQ) : DataQ (Fin 5) 5 :=
  { gram := fun i j => ∑ a, ∑ b,
      s.base.snapshot.centerMatrix i a * d.gram a b * s.base.snapshot.centerMatrix j b
    value := fun i => d.values (s.base.ordering.values.toSource i).castSucc
    position := (Profiles.ProximalGradient.modelQ 0).position
    gradient := (Profiles.ProximalGradient.modelQ 0).gradient }

/-- Actual primal congruence, in the source's native leaf order. This is C G Cᵀ,
not the dual restriction Jᵀ S J. Values gather the five sample slots, excluding tau. -/
theorem primal_transport (s : ProximalGradientSparse.SourceQ 0 10) (d : NativeQ)
    (i j : Fin 5) :
    (castDataQ (canonicalData s d)).gram i j =
      ∑ a, ∑ b, (s.base.snapshot.centerMatrix i a : ℝ) *
        (d.gram a b : ℝ) * (s.base.snapshot.centerMatrix j b : ℝ) := by
  simp [canonicalData, castDataQ, castGramQ]

def beta (d : NativeQ) : ℚ := d.values 4 + d.values 3 - (d.values 0 + d.values 1)

/-- A thin conjunction of existing complete finite checks. Source/trace and
raw-policy binding are separate obligations, checked concretely in each Replay. -/
def checkFinite (s : ProximalGradientSparse.SourceQ 0 10)
    (t : ProximalGradientCapture.TraceQ 0 10) (d : NativeQ)
    (nf : PSDFactorCertQ 6) (cf : PSDFactorCertQ 5) : Bool :=
  checkPSDFactorQ d.gram nf && checkAssumptionsFeasibleQ (nativeModel t) d.data &&
    checkPSDFactorQ (canonicalData s d).gram cf &&
    checkAssumptionsFeasibleQ (Profiles.ProximalGradient.modelQ 0) (canonicalData s d) &&
    decide (d.values 5 ≤ beta d ∧
      (Profiles.ProximalGradient.objectiveQ 0).evalQ (canonicalData s d) = beta d ∧ 0 < beta d)

theorem checkFinite_sound (s : ProximalGradientSparse.SourceQ 0 10)
    (t : ProximalGradientCapture.TraceQ 0 10) (d : NativeQ)
    (nf : PSDFactorCertQ 6) (cf : PSDFactorCertQ 5)
    (h : checkFinite s t d nf cf = true) :
    IsGramPosSemidef (castDataQ d.data).gram ∧
    AssumptionsFeasibleR (nativeModel t) (castDataQ d.data) ∧
    IsGramPosSemidef (castDataQ (canonicalData s d)).gram ∧
    AssumptionsFeasibleR (Profiles.ProximalGradient.modelQ 0) (castDataQ (canonicalData s d)) ∧
    (Profiles.ProximalGradient.objectiveQ 0).evalR (castDataQ (canonicalData s d)) = (beta d : ℝ) ∧
    0 < (beta d : ℝ) := by
  simp only [checkFinite, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  rcases h with ⟨hn, ha, hc, hf, ht, ho, hb⟩
  refine ⟨checkPSDFactorQ_sound_real _ _ hn,
    assumptionsFeasibleQ_toReal _ _ ((checkAssumptionsFeasibleQ_eq_true_iff _ _).mp ha),
    checkPSDFactorQ_sound_real _ _ hc,
    assumptionsFeasibleQ_toReal _ _ ((checkAssumptionsFeasibleQ_eq_true_iff _ _).mp hf), ?_,
    Rat.cast_pos.mpr hb⟩
  rw [LinearExprQ.evalR_castDataQ, ho]

end LeanPEP.Adapters.PGOnePrimal
