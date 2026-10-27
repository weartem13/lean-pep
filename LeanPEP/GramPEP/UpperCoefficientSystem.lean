import LeanPEP.GramPEP.RationalLinearSystem
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! D12: a Lean-defined compiler for a fixed objective, residual, and ordered
assumption-reference family. Rows are constant, all values, and ALL ordered
Gram entries. Columns are bound and one weight per occurrence, including
repeated/zero rows. No solver, source parser, or floating arithmetic is trusted.
This module has no optimization-profile-specific formulas. -/
namespace LeanPEP.GramPEP.UpperCoefficientSystem
open scoped BigOperators
open RationalLinearSystem (SystemQ IsSolutionQ)

def rowCount (p m : ℕ) : ℕ := p + m * m + 1

/-- Row-major coefficients: constant, values, then ordered Gram pairs. -/
def coefficientQ {p m : ℕ} (e : LinearExprQ p m) : Fin (rowCount p m) → ℚ :=
  Fin.cases e.constCoeff (Fin.addCases e.valueCoeff
    (fun k : Fin (m * m) => e.gramCoeff (finProdFinEquiv.symm k).1
      (finProdFinEquiv.symm k).2))

@[simp] theorem coefficient_zero {p m : ℕ} (i : Fin (rowCount p m)) :
    coefficientQ (LinearExprQ.zero p m) i = 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      simp [coefficientQ, LinearExprQ.zero]

@[simp] theorem coefficient_add {p m : ℕ} (a b : LinearExprQ p m)
    (i : Fin (rowCount p m)) :
    coefficientQ (a.add b) i = coefficientQ a i + coefficientQ b i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      simp [coefficientQ, LinearExprQ.add]

@[simp] theorem coefficient_scale {p m : ℕ} (a : ℚ) (e : LinearExprQ p m)
    (i : Fin (rowCount p m)) :
    coefficientQ (LinearExprQ.scale a e) i = a * coefficientQ e i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      simp [coefficientQ, LinearExprQ.scale]

@[simp] theorem coefficient_target {p m : ℕ} (b : ℚ) (e : LinearExprQ p m)
    (i : Fin (rowCount p m)) :
    coefficientQ (upperTargetExprQ b e) i =
      coefficientQ (LinearExprQ.const p m 1) i * b - coefficientQ e i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [coefficientQ, upperTargetExprQ, LinearExprQ.sub, LinearExprQ.add,
      LinearExprQ.neg, LinearExprQ.const, sub_eq_add_neg]
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      simp [coefficientQ, upperTargetExprQ, LinearExprQ.sub, LinearExprQ.add,
        LinearExprQ.neg, LinearExprQ.const]

/-- No off-diagonal coefficient is forgotten, even on nonsymmetric data. -/
theorem coefficient_ext_iff {p m : ℕ} (a b : LinearExprQ p m) :
    a = b ↔ ∀ i, coefficientQ a i = coefficientQ b i := by
  constructor
  · rintro rfl i
    rfl
  · intro h
    apply LinearExprQ.ext
    · exact h ⟨0, Nat.zero_lt_succ (p + m * m)⟩
    · funext i
      simpa [coefficientQ] using h (Fin.succ (Fin.castAdd (m * m) i))
    · funext i j
      simpa only [coefficientQ, Fin.cases_succ, Fin.addCases_right,
        Equiv.symm_apply_apply] using
        h (Fin.succ (Fin.natAdd p (finProdFinEquiv (i, j))))

/-- Fixed family: q counts occurrences, not distinct referenced rows. -/
structure FamilyQ {p m : ℕ} (model : ModelQ p m) (q : ℕ) where
  objective : LinearExprQ p m
  residual : Gram m ℚ
  factors : PSDFactorCertQ m
  references : Fin q → Fin model.assumptions.length

def ofUpperQ {p m : ℕ} {model : ModelQ p m} (seed : UpperCertQ model) :
    FamilyQ model seed.assumptionTerms.length :=
  { objective := seed.objective
    residual := seed.dualMatrix
    factors := seed.dualFactor
    references := fun j => (seed.assumptionTerms.get j).index }

/-- x[0] is the bound; x[j+1] is the j-th multiplier. No implicit interpolation. -/
def instantiateQ {p m q : ℕ} {model : ModelQ p m} (f : FamilyQ model q)
    (x : Fin (q + 1) → ℚ) : UpperCertQ model :=
  { bound := x 0
    objective := f.objective
    interpTerms := []
    assumptionTerms := List.ofFn fun j => { weight := x j.succ, index := f.references j }
    dualMatrix := f.residual
    dualFactor := f.factors }

/-- beta - sum lambda*row = objective + residual, coefficient by coefficient. -/
def compileQ {p m q : ℕ} {model : ModelQ p m} (f : FamilyQ model q) :
    SystemQ (rowCount p m) (q + 1) :=
  { matrix := fun i => Fin.cases (coefficientQ (LinearExprQ.const p m 1) i)
      (fun j => -coefficientQ (model.assumptions.get (f.references j)) i)
    rhs := fun i => coefficientQ f.objective i +
      coefficientQ (LinearExprQ.gramPairing f.residual) i }

theorem coefficient_assumptions {p m q : ℕ} (model : ModelQ p m)
    (ts : Fin q → AssumptionTermQ model) (i : Fin (rowCount p m)) :
    coefficientQ (assumptionExprSumQ model (List.ofFn ts)) i =
      ∑ j, (ts j).weight * coefficientQ (model.assumptions.get (ts j).index) i := by
  induction q with
  | zero => simp [assumptionExprSumQ]
  | succ q ih =>
      rw [List.ofFn_succ, assumptionExprSumQ, coefficient_add, coefficient_scale,
        ih (fun j => ts j.succ), Fin.sum_univ_succ]

theorem coefficient_rhs {p m q : ℕ} {model : ModelQ p m} (f : FamilyQ model q)
    (x : Fin (q + 1) → ℚ) (i : Fin (rowCount p m)) :
    coefficientQ (certificateRhsExprQ (instantiateQ f x)) i =
      (∑ j, x j.succ * coefficientQ (model.assumptions.get (f.references j)) i) +
        coefficientQ (LinearExprQ.gramPairing f.residual) i := by
  simp [certificateRhsExprQ, instantiateQ, interpExprSumQ, coefficient_assumptions]

theorem compile_row {p m q : ℕ} {model : ModelQ p m} (f : FamilyQ model q)
    (x : Fin (q + 1) → ℚ) (i : Fin (rowCount p m)) :
    (∑ j, (compileQ f).matrix i j * x j) =
      coefficientQ (LinearExprQ.const p m 1) i * x 0 -
        ∑ j, x j.succ * coefficientQ (model.assumptions.get (f.references j)) i := by
  simp [compileQ, Fin.sum_univ_succ, neg_mul, Finset.sum_neg_distrib,
    sub_eq_add_neg, mul_comm]

/-- The source-to-system bridge, independent of signs, PSD and feasibility. -/
theorem identity_iff_solution {p m q : ℕ} {model : ModelQ p m} (f : FamilyQ model q)
    (x : Fin (q + 1) → ℚ) :
    certificateRhsExprQ (instantiateQ f x) = upperTargetExprQ (x 0) f.objective ↔
      IsSolutionQ (compileQ f) x := by
  rw [coefficient_ext_iff]
  constructor
  · intro h i
    have hi := h i
    rw [coefficient_rhs, coefficient_target] at hi
    rw [compile_row]
    change _ = coefficientQ f.objective i + coefficientQ (LinearExprQ.gramPairing f.residual) i
    linarith only [hi]
  · intro h i
    have hi := h i
    rw [compile_row] at hi
    change _ = coefficientQ f.objective i + coefficientQ (LinearExprQ.gramPairing f.residual) i at hi
    rw [coefficient_rhs, coefficient_target]
    linarith only [hi]

theorem weights_nonnegative_iff {p m q : ℕ} {model : ModelQ p m}
    (f : FamilyQ model q) (x : Fin (q + 1) → ℚ) :
    (∀ t ∈ (instantiateQ f x).assumptionTerms, 0 ≤ t.weight) ↔
      ∀ j : Fin q, 0 ≤ x j.succ := by
  constructor
  · intro h j
    exact h _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  · intro h t ht
    rcases List.mem_ofFn.mp ht with ⟨j, rfl⟩
    exact h j

/-- Exact equations plus nonnegative weights and the ORIGINAL PSD obligation. -/
theorem accepted_iff {p m q : ℕ} {model : ModelQ p m} (f : FamilyQ model q)
    (x : Fin (q + 1) → ℚ) :
    checkUpperCertQ (instantiateQ f x) = true ↔
      IsSolutionQ (compileQ f) x ∧ (∀ j : Fin q, 0 ≤ x j.succ) ∧
        PSDFactorValidQ f.residual f.factors := by
  constructor
  · intro hc
    have h := checkUpperCertQ_sound _ hc
    exact ⟨(identity_iff_solution f x).mp h.identity,
      (weights_nonnegative_iff f x).mp h.assumptionWeights, h.dualValid⟩
  · rintro ⟨hs, hw, hp⟩
    apply checkUpperCertQ_complete
    exact
      { interpWeights := by simp [instantiateQ]
        assumptionWeights := (weights_nonnegative_iff f x).mpr hw
        dualValid := hp
        identity := (identity_iff_solution f x).mpr hs }

/-- Bind every entry of an untrusted emitted system to the Lean compiler. -/
def checkSystemQ {p m q : ℕ} {model : ModelQ p m} (f : FamilyQ model q)
    (s : SystemQ (rowCount p m) (q + 1)) : Bool :=
  (List.finRange (rowCount p m)).all fun i =>
    decide (s.rhs i = (compileQ f).rhs i) &&
      (List.finRange (q + 1)).all (fun j => decide (s.matrix i j = (compileQ f).matrix i j))

theorem checkSystemQ_eq_true_iff {p m q : ℕ} {model : ModelQ p m}
    (f : FamilyQ model q) (s : SystemQ (rowCount p m) (q + 1)) :
    checkSystemQ f s = true ↔ s = compileQ f := by
  have h : checkSystemQ f s = true ↔ ∀ i,
      s.rhs i = (compileQ f).rhs i ∧ ∀ j, s.matrix i j = (compileQ f).matrix i j := by
    simp [checkSystemQ, List.all_eq_true]
  rw [h]
  constructor
  · intro hs
    have hm : s.matrix = (compileQ f).matrix := funext fun i => funext (hs i).2
    have hb : s.rhs = (compileQ f).rhs := funext fun i => (hs i).1
    cases s
    cases hm
    cases hb
    rfl
  · rintro rfl i
    exact ⟨rfl, fun _ => rfl⟩

/-- An audited system obstruction rules out EVERY bound/weight choice in this
fixed family, not merely the submitted vector. No PSD assumption is needed. -/
theorem checked_no_identity {p m q : ℕ} {model : ModelQ p m}
    (f : FamilyQ model q) (s : SystemQ (rowCount p m) (q + 1))
    (hs : checkSystemQ f s = true) (y : Fin (rowCount p m) → ℚ)
    (hy : RationalLinearSystem.checkObstructionQ s y = true) :
    ¬ ∃ x, certificateRhsExprQ (instantiateQ f x) = upperTargetExprQ (x 0) f.objective := by
  have he := (checkSystemQ_eq_true_iff f s).mp hs
  rintro ⟨x, hx⟩
  apply RationalLinearSystem.checked_obstruction s y hy
  exact ⟨x, he.symm ▸ (identity_iff_solution f x).mp hx⟩

theorem checked_no_accepted {p m q : ℕ} {model : ModelQ p m}
    (f : FamilyQ model q) (s : SystemQ (rowCount p m) (q + 1))
    (hs : checkSystemQ f s = true) (y : Fin (rowCount p m) → ℚ)
    (hy : RationalLinearSystem.checkObstructionQ s y = true) :
    ¬ ∃ x, checkUpperCertQ (instantiateQ f x) = true := by
  rintro ⟨x, hx⟩
  exact checked_no_identity f s hs y hy ⟨x, (checkUpperCertQ_sound _ hx).identity⟩

end LeanPEP.GramPEP.UpperCoefficientSystem
