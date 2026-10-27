import LeanPEP.Adapters.ProximalGradientRows
import LeanPEP.GramPEP.PerformanceLift

/-!
# D6: a single maximized performance variable, with a fully checked lifting

Scalar slot 0 is tau, row 0 is the signed/positively scaled performance row.
All old scalar slots and rows are shifted by one; their D5 storage order remains.
The source contains ACTUAL submitted extended rows and objective. They are not
silently reconstructed before checking. Only the declared performance row can
be removed, after substitution proves its complete polynomial is zero.
-/
namespace LeanPEP.Adapters.ProximalGradientPerformance

open LeanPEP.GramPEP LeanPEP.GramPEP.PerformanceLift LeanPEP.GramPEP.RowNormalization
open ProximalGradientOrdering (valueCount basisCount rowCount)

@[ext] structure SourceQ (n : ℕ) where
  base : ProximalGradientRows.SourceQ n
  performanceRule : RuleQ
  rows : Fin (rowCount n + 1) → LinearExprQ (valueCount n + 1) (basisCount n)
  objective : LinearExprQ (valueCount n + 1) (basisCount n)

def expectedRowsQ {n : ℕ} (b : ProximalGradientRows.SourceQ n) (r : RuleQ) :
    Fin (rowCount n + 1) → LinearExprQ (valueCount n + 1) (basisCount n) :=
  Fin.cons (encodeExprQ r (linkExprQ b.snapshot.objective))
    (fun i => embedExprQ (b.snapshot.constraints i))

def rowRuleQ {n : ℕ} (s : SourceQ n) : Fin (rowCount n + 1) → RuleQ :=
  Fin.cons s.performanceRule s.base.rules

def orientedRowQ {n : ℕ} (s : SourceQ n) (i : Fin (rowCount n + 1)) :
    LinearExprQ (valueCount n + 1) (basisCount n) :=
  orientExprQ (rowRuleQ s i).sense (s.rows i)

def SourceQ.model {n : ℕ} (s : SourceQ n) : ModelQ (valueCount n + 1) (basisCount n) :=
  { position := fun _ => 0
    gradient := fun _ => 0
    assumptions := List.ofFn (orientedRowQ s) }

def checkLiftQ {n : ℕ} (s : SourceQ n) : Bool :=
  decide (0 < s.performanceRule.scale) &&
    ((List.finRange (rowCount n + 1)).all
      (fun i => checkLinearExprEqQ (s.rows i) (expectedRowsQ s.base s.performanceRule i)) &&
      checkLinearExprEqQ s.objective (tauExprQ (valueCount n) (basisCount n)))

theorem checkLiftQ_eq_true_iff {n : ℕ} (s : SourceQ n) :
    checkLiftQ s = true ↔ 0 < s.performanceRule.scale ∧
      (∀ i, s.rows i = expectedRowsQ s.base s.performanceRule i) ∧
      s.objective = tauExprQ (valueCount n) (basisCount n) := by
  simp [checkLiftQ, List.all_eq_true, checkLinearExprEqQ_eq_true_iff]

def checkSourceQ {n : ℕ} (s : SourceQ n) : Bool :=
  ProximalGradientRows.checkSourceQ s.base && checkLiftQ s

theorem checkSourceQ_eq_true_iff {n : ℕ} (s : SourceQ n) :
    checkSourceQ s = true ↔ ProximalGradientRows.checkSourceQ s.base = true ∧ checkLiftQ s = true := by
  simp only [checkSourceQ, Bool.and_eq_true]

theorem oriented_zero {n : ℕ} (s : SourceQ n) (hs : checkLiftQ s = true) :
    orientedRowQ s 0 = LinearExprQ.scale s.performanceRule.scale (linkExprQ s.base.snapshot.objective) := by
  have he := ((checkLiftQ_eq_true_iff s).mp hs).2.1 0
  change orientExprQ s.performanceRule.sense (s.rows 0) = _
  rw [he]
  exact orient_involutive s.performanceRule.sense _

theorem oriented_succ {n : ℕ} (s : SourceQ n) (hs : checkLiftQ s = true) (i : Fin (rowCount n)) :
    orientedRowQ s i.succ = embedExprQ
      (orientExprQ (s.base.rules i).sense (s.base.snapshot.constraints i)) := by
  have he := ((checkLiftQ_eq_true_iff s).mp hs).2.1 i.succ
  change orientExprQ (s.base.rules i).sense (s.rows i.succ) = _
  rw [he]
  exact (embed_orient (s.base.rules i).sense (s.base.snapshot.constraints i)).symm

@[simp] theorem substitute_row_zero {n : ℕ} (s : SourceQ n) (hs : checkLiftQ s = true) :
    substituteQ s.base.snapshot.objective (orientedRowQ s 0) = LinearExprQ.zero _ _ := by
  rw [oriented_zero s hs, substitute_scale, substitute_link, expr_scale_zero]

@[simp] theorem substitute_row_succ {n : ℕ} (s : SourceQ n) (hs : checkLiftQ s = true)
    (i : Fin (rowCount n)) :
    substituteQ s.base.snapshot.objective (orientedRowQ s i.succ) =
      orientExprQ (s.base.rules i).sense (s.base.snapshot.constraints i) := by
  rw [oriented_succ s hs, substitute_embed]

/-- Feasibility is preserved by choosing tau=metric, not by fixing tau=0.
No PSD or realizability is needed for this pointwise row equivalence. -/
theorem rows_feasible_iff {n : ℕ} (s : SourceQ n) (hs : checkLiftQ s = true)
    (d : DataR (Fin (valueCount n)) (basisCount n)) (t : ℝ) :
    (∀ i, 0 ≤ (orientedRowQ s i).evalR (extendDataR d t)) ↔
      (∀ i, HoldsR (s.base.rules i).sense (s.base.snapshot.constraints i) d) ∧
      t ≤ s.base.snapshot.objective.evalR d := by
  have hpQ := ((checkLiftQ_eq_true_iff s).mp hs).1
  have hp : 0 < (s.performanceRule.scale : ℝ) := by exact_mod_cast hpQ
  have hz : 0 ≤ (orientedRowQ s 0).evalR (extendDataR d t) ↔
      t ≤ s.base.snapshot.objective.evalR d := by
    rw [oriented_zero s hs, LinearExprQ.evalR_scale, eval_link]
    constructor
    · intro h
      have hprod : (s.performanceRule.scale : ℝ) * 0 ≤
          (s.performanceRule.scale : ℝ) * (s.base.snapshot.objective.evalR d - t) := by
        simpa only [mul_zero] using h
      exact sub_nonneg.mp (le_of_mul_le_mul_left hprod hp)
    · intro h
      exact mul_nonneg (le_of_lt hp) (sub_nonneg.mpr h)
  constructor
  · intro h
    refine ⟨?_, hz.mp (h 0)⟩
    intro i
    apply (orient_nonneg_iff (s.base.rules i).sense (s.base.snapshot.constraints i) d).mp
    have hi := h i.succ
    simpa only [oriented_succ s hs, eval_embed] using hi
  · rintro ⟨h, ht⟩ i
    refine Fin.cases (hz.mpr ht) (fun j => ?_) i
    rw [oriented_succ s hs, eval_embed]
    exact (orient_nonneg_iff _ _ _).mpr (h j)

/-- All scalar upper bounds are equivalent, independently of certificate construction. -/
theorem finite_upper_equivalence {n : ℕ} (s : SourceQ n) (hs : checkLiftQ s = true) (B : ℝ) :
    (∀ d : DataR (Fin (valueCount n)) (basisCount n), IsGramPosSemidef d.gram →
      (∀ i, HoldsR (s.base.rules i).sense (s.base.snapshot.constraints i) d) →
      s.base.snapshot.objective.evalR d ≤ B) ↔
    (∀ (d : DataR (Fin (valueCount n)) (basisCount n)) (t : ℝ), IsGramPosSemidef d.gram →
      (∀ i, 0 ≤ (orientedRowQ s i).evalR (extendDataR d t)) → t ≤ B) := by
  constructor
  · intro h d t hG hr
    obtain ⟨hb, ht⟩ := (rows_feasible_iff s hs d t).mp hr
    exact ht.trans (h d hG hb)
  · intro h d hG hb
    exact h d (s.base.snapshot.objective.evalR d) hG
      ((rows_feasible_iff s hs d _).mpr ⟨hb, le_refl _⟩)

def sourceRowQ {n : ℕ} (s : SourceQ n) (t : AssumptionTermQ s.model) : Fin (rowCount n + 1) :=
  ⟨t.index.val, by simpa only [SourceQ.model, List.length_ofFn] using t.index.isLt⟩

def baseTermQ {n : ℕ} (s : SourceQ n) (i : Fin (rowCount n)) (w : ℚ) : AssumptionTermQ s.base.model :=
  { weight := w
    index := ⟨i.val, by simpa only [ProximalGradientRows.SourceQ.model, List.length_ofFn] using i.isLt⟩ }

def eliminateConsQ {n : ℕ} (s : SourceQ n) (i : Fin (rowCount n + 1)) (w : ℚ)
    (rest : List (AssumptionTermQ s.base.model)) : List (AssumptionTermQ s.base.model) :=
  Fin.cases rest (fun j => baseTermQ s j w :: rest) i

def eliminateTermsQ {n : ℕ} (s : SourceQ n) :
    List (AssumptionTermQ s.model) → List (AssumptionTermQ s.base.model)
  | [] => []
  | t :: ts => eliminateConsQ s (sourceRowQ s t) t.weight (eliminateTermsQ s ts)

theorem base_get {n : ℕ} (s : SourceQ n) (i : Fin (rowCount n)) (w : ℚ) :
    s.base.model.assumptions.get (baseTermQ s i w).index =
      orientExprQ (s.base.rules i).sense (s.base.snapshot.constraints i) := by
  exact List.get_ofFn
    (fun j => orientExprQ (s.base.rules j).sense (s.base.snapshot.constraints j)) (baseTermQ s i w).index

theorem source_get {n : ℕ} (s : SourceQ n) (t : AssumptionTermQ s.model) :
    s.model.assumptions.get t.index = orientedRowQ s (sourceRowQ s t) := by
  exact List.get_ofFn (orientedRowQ s) t.index

/-- Only index 0 (the declared performance row) disappears. All other weights
and their order, including zero weights and repeated references, are retained. -/
theorem eliminate_cons_sum {n : ℕ} (s : SourceQ n) (hs : checkLiftQ s = true)
    (i : Fin (rowCount n + 1)) (w : ℚ) (rest : List (AssumptionTermQ s.base.model)) :
    assumptionExprSumQ s.base.model (eliminateConsQ s i w rest) =
      LinearExprQ.add (LinearExprQ.scale w (substituteQ s.base.snapshot.objective (orientedRowQ s i)))
        (assumptionExprSumQ s.base.model rest) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [eliminateConsQ, substitute_row_zero s hs]
  · change LinearExprQ.add
        (LinearExprQ.scale w (s.base.model.assumptions.get (baseTermQ s j w).index))
        (assumptionExprSumQ s.base.model rest) = _
    rw [base_get, substitute_row_succ s hs]

theorem assumption_sum_preserved {n : ℕ} (s : SourceQ n) (hs : checkLiftQ s = true)
    (ts : List (AssumptionTermQ s.model)) :
    substituteQ s.base.snapshot.objective (assumptionExprSumQ s.model ts) =
      assumptionExprSumQ s.base.model (eliminateTermsQ s ts) := by
  induction ts with
  | nil => exact substitute_zero _
  | cons t ts ih =>
      simp only [assumptionExprSumQ, substitute_add, substitute_scale, source_get,
        eliminateTermsQ, eliminate_cons_sum s hs, ih]

theorem eliminate_cons_weights {n : ℕ} (s : SourceQ n) (i : Fin (rowCount n + 1))
    (w : ℚ) (hw : 0 ≤ w) (rest : List (AssumptionTermQ s.base.model))
    (hr : ∀ t ∈ rest, 0 ≤ t.weight) :
    ∀ t ∈ eliminateConsQ s i w rest, 0 ≤ t.weight := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hr
  · intro t ht
    change t ∈ baseTermQ s j w :: rest at ht
    rcases List.mem_cons.mp ht with he | he
    · subst t; exact hw
    · exact hr t he

theorem eliminate_weights {n : ℕ} (s : SourceQ n) (ts : List (AssumptionTermQ s.model))
    (hw : ∀ t ∈ ts, 0 ≤ t.weight) : ∀ t ∈ eliminateTermsQ s ts, 0 ≤ t.weight := by
  revert hw
  induction ts with
  | nil => intro hw; simp [eliminateTermsQ]
  | cons t ts ih =>
      intro hw
      exact eliminate_cons_weights s (sourceRowQ s t) t.weight (hw t (by simp)) _
        (ih (fun u hu => hw u (by simp [hu])))

/-- Empty implicit interpolation is an explicit PRECONDITION to sound transport.
The total data function below never grants acceptance to nonempty input. -/
def eliminatedUpperQ {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) : UpperCertQ s.base.model :=
  { bound := c.bound
    objective := substituteQ s.base.snapshot.objective c.objective
    interpTerms := []
    assumptionTerms := eliminateTermsQ s c.assumptionTerms
    dualMatrix := c.dualMatrix
    dualFactor := c.dualFactor }

@[simp] theorem eliminatedUpperQ_bound {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) :
    (eliminatedUpperQ s c).bound = c.bound := rfl

theorem certificate_rhs_preserved {n : ℕ} (s : SourceQ n) (hs : checkLiftQ s = true)
    (c : UpperCertQ s.model) (hi : c.interpTerms = []) :
    substituteQ s.base.snapshot.objective (certificateRhsExprQ c) =
      certificateRhsExprQ (eliminatedUpperQ s c) := by
  simp only [certificateRhsExprQ, hi, interpExprSumQ, eliminatedUpperQ,
    substitute_add, substitute_zero, substitute_gramPairing, assumption_sum_preserved s hs]

/-- Accepted extended certificates retain acceptance under exact substitution.
No known rate, accepted base certificate or numerical tolerance is assumed. -/
theorem eliminatedUpper_check {n : ℕ} (s : SourceQ n) (hs : checkLiftQ s = true)
    (c : UpperCertQ s.model) (hi : c.interpTerms = []) (hc : checkUpperCertQ c = true) :
    checkUpperCertQ (eliminatedUpperQ s c) = true := by
  have hv := checkUpperCertQ_sound c hc
  apply checkUpperCertQ_complete
  refine
    { interpWeights := by simp [eliminatedUpperQ]
      assumptionWeights := eliminate_weights s c.assumptionTerms hv.assumptionWeights
      dualValid := hv.dualValid
      identity := ?_ }
  have he := congrArg (substituteQ s.base.snapshot.objective) hv.identity
  rw [certificate_rhs_preserved s hs c hi] at he
  simpa only [upperTargetExprQ, LinearExprQ.sub, substitute_add, substitute_neg,
    substitute_const, eliminatedUpperQ] using he

/-- Complete weight on the performance row, allowing duplicate references. -/
def performanceMassQ {n : ℕ} (s : SourceQ n) : List (AssumptionTermQ s.model) → ℚ
  | [] => 0
  | t :: ts => (if sourceRowQ s t = 0 then t.weight * s.performanceRule.scale else 0) +
      performanceMassQ s ts

theorem oriented_tau_coeff {n : ℕ} (s : SourceQ n) (hs : checkLiftQ s = true)
    (i : Fin (rowCount n + 1)) :
    (orientedRowQ s i).valueCoeff 0 = if i = 0 then -s.performanceRule.scale else 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [oriented_zero s hs]
    simp [linkExprQ, embedExprQ, tauExprQ, LinearExprQ.scale, LinearExprQ.sub, LinearExprQ.add, LinearExprQ.neg]
  · rw [oriented_succ s hs]
    simp [embedExprQ, Fin.succ_ne_zero]

theorem assumption_tau_coeff {n : ℕ} (s : SourceQ n) (hs : checkLiftQ s = true)
    (ts : List (AssumptionTermQ s.model)) :
    (assumptionExprSumQ s.model ts).valueCoeff 0 = -performanceMassQ s ts := by
  induction ts with
  | nil => simp [assumptionExprSumQ, LinearExprQ.zero, performanceMassQ]
  | cons t ts ih =>
      simp only [assumptionExprSumQ, LinearExprQ.add, LinearExprQ.scale, source_get,
        oriented_tau_coeff s hs, performanceMassQ, ih]
      split_ifs <;> ring

/-- Derived from the tau coefficient of the FULL checked identity. For a
single link reference this says lambda*scale=1, NOT lambda=1 in every convention. -/
theorem performance_mass_eq_one {n : ℕ} (s : SourceQ n) (hs : checkLiftQ s = true)
    (c : UpperCertQ s.model) (hi : c.interpTerms = [])
    (ho : c.objective = tauExprQ (valueCount n) (basisCount n)) (hc : checkUpperCertQ c = true) :
    performanceMassQ s c.assumptionTerms = 1 := by
  have hv := checkUpperCertQ_sound c hc
  have he : (certificateRhsExprQ c).valueCoeff 0 = (upperTargetExprQ c.bound c.objective).valueCoeff 0 :=
    congrArg (fun e : LinearExprQ (valueCount n + 1) (basisCount n) => e.valueCoeff 0) hv.identity
  have hl : (certificateRhsExprQ c).valueCoeff 0 = -performanceMassQ s c.assumptionTerms := by
    simp only [certificateRhsExprQ, hi, interpExprSumQ, LinearExprQ.add, LinearExprQ.zero,
      LinearExprQ.gramPairing, assumption_tau_coeff s hs, zero_add, add_zero]
  have hr : (upperTargetExprQ c.bound c.objective).valueCoeff 0 = -1 := by
    rw [ho]
    simp [upperTargetExprQ, LinearExprQ.sub, LinearExprQ.add, LinearExprQ.neg, LinearExprQ.const, tauExprQ]
  rw [hl, hr] at he
  linarith only [he]

/-- No guard is weakened: raw extended checker, exact objective, empty implicit
interpolation, and the entire original D5/D4/D3/D2 chain all remain required. -/
def checkBoundQ {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) : Bool :=
  checkSourceQ s && (checkUpperCertQ c && (decide (c.interpTerms = []) &&
    (checkLinearExprEqQ c.objective s.objective &&
      ProximalGradientRows.checkBoundQ s.base (eliminatedUpperQ s c))))

theorem checkBoundQ_eq_true_iff {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) :
    checkBoundQ s c = true ↔ checkSourceQ s = true ∧ checkUpperCertQ c = true ∧
      c.interpTerms = [] ∧ c.objective = s.objective ∧
      ProximalGradientRows.checkBoundQ s.base (eliminatedUpperQ s c) = true := by
  simp only [checkBoundQ, Bool.and_eq_true, decide_eq_true_eq, checkLinearExprEqQ_eq_true_iff]

theorem checked_performance_mass {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model)
    (hc : checkBoundQ s c = true) : performanceMassQ s c.assumptionTerms = 1 := by
  have h := (checkBoundQ_eq_true_iff s c).mp hc
  have hs := ((checkSourceQ_eq_true_iff s).mp h.1).2
  have ho := ((checkLiftQ_eq_true_iff s).mp hs).2.2
  exact performance_mass_eq_one s hs c h.2.2.1 (h.2.2.2.1.trans ho) h.2.1

theorem checked_certificate {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) (hc : checkBoundQ s c = true) :
    ∃ d : UpperCertQ (Profiles.ProximalGradient.modelQ n), checkUpperCertQ d = true ∧
      d.interpTerms = [] ∧ d.objective = Profiles.ProximalGradient.objectiveQ n ∧ d.bound = c.bound := by
  exact ProximalGradientRows.checked_certificate s.base (eliminatedUpperQ s c)
    (((checkBoundQ_eq_true_iff s c).mp hc).2.2.2.2)

end LeanPEP.Adapters.ProximalGradientPerformance
