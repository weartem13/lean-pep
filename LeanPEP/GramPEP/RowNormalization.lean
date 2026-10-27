import LeanPEP.GramPEP.UpperCertificateChecker

/-!
# D5: signed row conventions and strictly positive rational row normalization

A raw row is q >= 0 or q <= 0. Its oriented expression is respectively q or -q.
The oriented expression equals `scale * normalized`. A certificate multiplier
on the oriented raw row therefore becomes `weight * scale`, never weight/scale.
The reverse operation used to CREATE test inputs divides the multiplier.
No constraints, constants, off-diagonal entries, or zero-weight terms are dropped.
-/
namespace LeanPEP.GramPEP.RowNormalization

inductive SenseQ where
  | geZero
  | leZero
  deriving DecidableEq, Repr

@[ext] structure RuleQ where
  sense : SenseQ
  scale : ℚ
  deriving DecidableEq, Repr

def checkRulesQ {k : ℕ} (rs : Fin k → RuleQ) : Bool :=
  (List.finRange k).all (fun i => decide (0 < (rs i).scale))

theorem checkRulesQ_eq_true_iff {k : ℕ} (rs : Fin k → RuleQ) :
    checkRulesQ rs = true ↔ ∀ i, 0 < (rs i).scale := by
  simp [checkRulesQ, List.all_eq_true]

def orientExprQ {p m : ℕ} (sense : SenseQ) (e : LinearExprQ p m) : LinearExprQ p m :=
  match sense with
  | .geZero => e
  | .leZero => LinearExprQ.neg e

def normalizeExprQ {p m : ℕ} (r : RuleQ) (e : LinearExprQ p m) : LinearExprQ p m :=
  LinearExprQ.scale r.scale⁻¹ (orientExprQ r.sense e)

def encodeExprQ {p m : ℕ} (r : RuleQ) (e : LinearExprQ p m) : LinearExprQ p m :=
  orientExprQ r.sense (LinearExprQ.scale r.scale e)

theorem scale_scale {p m : ℕ} (a b : ℚ) (e : LinearExprQ p m) :
    LinearExprQ.scale a (LinearExprQ.scale b e) = LinearExprQ.scale (a*b) e := by
  apply LinearExprQ.ext
  · simp [LinearExprQ.scale, mul_assoc]
  · funext i; simp [LinearExprQ.scale, mul_assoc]
  · funext i j; simp [LinearExprQ.scale, mul_assoc]

theorem scale_one {p m : ℕ} (e : LinearExprQ p m) : LinearExprQ.scale 1 e = e := by
  apply LinearExprQ.ext
  · simp [LinearExprQ.scale]
  · funext i; simp [LinearExprQ.scale]
  · funext i j; simp [LinearExprQ.scale]

theorem orient_involutive {p m : ℕ} (sense : SenseQ) (e : LinearExprQ p m) :
    orientExprQ sense (orientExprQ sense e) = e := by
  cases sense with
  | geZero => rfl
  | leZero =>
      apply LinearExprQ.ext
      · simp [orientExprQ, LinearExprQ.neg]
      · funext i; simp [orientExprQ, LinearExprQ.neg]
      · funext i j; simp [orientExprQ, LinearExprQ.neg]

theorem scale_normalize {p m : ℕ} (r : RuleQ) (hr : r.scale ≠ 0) (e : LinearExprQ p m) :
    LinearExprQ.scale r.scale (normalizeExprQ r e) = orientExprQ r.sense e := by
  rw [normalizeExprQ, scale_scale, mul_inv_cancel₀ hr, scale_one]

theorem encode_normalize {p m : ℕ} (r : RuleQ) (hr : r.scale ≠ 0) (e : LinearExprQ p m) :
    encodeExprQ r (normalizeExprQ r e) = e := by
  rw [encodeExprQ, scale_normalize r hr, orient_involutive]

theorem normalize_encode {p m : ℕ} (r : RuleQ) (hr : r.scale ≠ 0) (e : LinearExprQ p m) :
    normalizeExprQ r (encodeExprQ r e) = e := by
  rw [normalizeExprQ, encodeExprQ, orient_involutive, scale_scale, inv_mul_cancel₀ hr, scale_one]

/-- Both inverse laws need nonzero scale, but preservation of inequalities needs POSITIVE scale. -/
theorem normalize_injective {p m : ℕ} (r : RuleQ) (hr : r.scale ≠ 0) :
    Function.Injective (normalizeExprQ (p := p) (m := m) r) := by
  intro e f h
  have hh := congrArg (encodeExprQ r) h
  simpa only [encode_normalize r hr] using hh

def HoldsR {p m : ℕ} (sense : SenseQ) (e : LinearExprQ p m) (d : DataR (Fin p) m) : Prop :=
  match sense with
  | .geZero => 0 ≤ e.evalR d
  | .leZero => e.evalR d ≤ 0

theorem orient_nonneg_iff {p m : ℕ} (sense : SenseQ) (e : LinearExprQ p m)
    (d : DataR (Fin p) m) :
    0 ≤ (orientExprQ sense e).evalR d ↔ HoldsR sense e d := by
  cases sense <;> simp [orientExprQ, HoldsR]

/-- Exact pointwise feasibility, for arbitrary real data, not just PSD/witness data. -/
theorem normalize_nonneg_iff {p m : ℕ} (r : RuleQ) (hr : 0 < r.scale)
    (e : LinearExprQ p m) (d : DataR (Fin p) m) :
    0 ≤ (normalizeExprQ r e).evalR d ↔ HoldsR r.sense e d := by
  have hpos : 0 < (r.scale : ℝ) := by exact_mod_cast hr
  constructor
  · intro hn
    apply (orient_nonneg_iff r.sense e d).mp
    rw [← scale_normalize r (ne_of_gt hr) e, LinearExprQ.evalR_scale]
    exact mul_nonneg (le_of_lt hpos) hn
  · intro hh
    have ho := (orient_nonneg_iff r.sense e d).mpr hh
    change 0 ≤ (LinearExprQ.scale r.scale⁻¹ (orientExprQ r.sense e)).evalR d
    rw [LinearExprQ.evalR_scale]
    have hi : 0 ≤ (r.scale⁻¹ : ℚ) := inv_nonneg.mpr (le_of_lt hr)
    exact mul_nonneg (by exact_mod_cast hi) ho

/-- Source lambda becomes lambda*scale; orientation is ALREADY in the source row. -/
theorem weighted_normalize {p m : ℕ} (r : RuleQ) (hr : r.scale ≠ 0)
    (w : ℚ) (e : LinearExprQ p m) :
    LinearExprQ.scale (w*r.scale) (normalizeExprQ r e) =
      LinearExprQ.scale w (orientExprQ r.sense e) := by
  rw [← scale_scale, scale_normalize r hr]

theorem normalized_weight_nonneg (r : RuleQ) (hr : 0 < r.scale) (w : ℚ) (hw : 0 ≤ w) :
    0 ≤ w*r.scale := mul_nonneg hw (le_of_lt hr)

end LeanPEP.GramPEP.RowNormalization
