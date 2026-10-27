import LeanPEP.GramPEP.UpperCoefficientSystem
import LeanPEP.GramPEP.RationalBoxSystem

/-! D12: link a submitted policy box to the original fixed certificate family.
Unlike D11's standalone obstruction, an accepted binding below connects the
negative conclusion to the ORIGINAL model/objective/residual/reference list.
Denominator bounds are deliberately not part of this continuous rational box.
A failure cannot rule out another residual, another reference list, or budget. -/
namespace LeanPEP.GramPEP.UpperCoefficientBox
open UpperCoefficientSystem
open RationalBoxSystem (BoxQ FeasibleQ)

/-- The bound can have either sign. Every assumption weight is nonnegative. -/
def signMaskQ (q : ℕ) : Fin (q + 1) → Bool := Fin.cases false (fun _ => true)

def WithinBudgetQ {q : ℕ} (raw x : Fin (q + 1) → ℚ) (eta : ℚ) : Prop :=
  ∀ j, |x j - raw j| ≤ eta

def compileBoxQ {p m q : ℕ} {model : ModelQ p m} (f : FamilyQ model q)
    (raw : Fin (q + 1) → ℚ) (eta : ℚ) : BoxQ (rowCount p m) (q + 1) :=
  { system := compileQ f
    lower := RationalBoxSystem.policyLowerQ raw eta (signMaskQ q)
    upper := RationalBoxSystem.policyUpperQ raw eta }

theorem feasible_iff {p m q : ℕ} {model : ModelQ p m} (f : FamilyQ model q)
    (raw x : Fin (q + 1) → ℚ) (eta : ℚ) :
    FeasibleQ (compileBoxQ f raw eta) x ↔
      RationalLinearSystem.IsSolutionQ (compileQ f) x ∧
      (∀ j : Fin q, 0 ≤ x j.succ) ∧ WithinBudgetQ raw x eta := by
  change FeasibleQ
    { system := compileQ f
      lower := RationalBoxSystem.policyLowerQ raw eta (signMaskQ q)
      upper := RationalBoxSystem.policyUpperQ raw eta } x ↔ _
  rw [RationalBoxSystem.policy_box_iff]
  constructor
  · rintro ⟨hs, h⟩
    refine ⟨hs, ?_, fun j => (h j).1⟩
    intro j
    exact (h j.succ).2 rfl
  · rintro ⟨hs, hw, hb⟩
    refine ⟨hs, fun j => ⟨hb j, ?_⟩⟩
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [signMaskQ]
    · intro _
      exact hw k

/-- The original PSD factor contract is exactly what a linear box alone lacks. -/
theorem feasible_iff_accepted {p m q : ℕ} {model : ModelQ p m} (f : FamilyQ model q)
    (raw x : Fin (q + 1) → ℚ) (eta : ℚ) (hp : PSDFactorValidQ f.residual f.factors) :
    FeasibleQ (compileBoxQ f raw eta) x ↔
      checkUpperCertQ (instantiateQ f x) = true ∧ WithinBudgetQ raw x eta := by
  rw [feasible_iff, accepted_iff]
  constructor
  · rintro ⟨hs, hw, hb⟩
    exact ⟨⟨hs, hw, hp⟩, hb⟩
  · rintro ⟨⟨hs, hw, _⟩, hb⟩
    exact ⟨hs, hw, hb⟩

/-- Both matrix/RHS and EVERY lower/upper endpoint are independently checked. -/
def checkBoxQ {p m q : ℕ} {model : ModelQ p m} (f : FamilyQ model q)
    (raw : Fin (q + 1) → ℚ) (eta : ℚ) (b : BoxQ (rowCount p m) (q + 1)) : Bool :=
  checkSystemQ f b.system &&
    (List.finRange (q + 1)).all (fun j =>
      decide (b.lower j = (compileBoxQ f raw eta).lower j ∧
        b.upper j = (compileBoxQ f raw eta).upper j))

theorem checkBoxQ_eq_true_iff {p m q : ℕ} {model : ModelQ p m} (f : FamilyQ model q)
    (raw : Fin (q + 1) → ℚ) (eta : ℚ) (b : BoxQ (rowCount p m) (q + 1)) :
    checkBoxQ f raw eta b = true ↔ b = compileBoxQ f raw eta := by
  have h : checkBoxQ f raw eta b = true ↔ b.system = compileQ f ∧
      ∀ j, b.lower j = (compileBoxQ f raw eta).lower j ∧
        b.upper j = (compileBoxQ f raw eta).upper j := by
    simp [checkBoxQ, checkSystemQ_eq_true_iff, List.all_eq_true]
  rw [h]
  constructor
  · rintro ⟨hs, hends⟩
    have hl : b.lower = (compileBoxQ f raw eta).lower := funext fun j => (hends j).1
    have hu : b.upper = (compileBoxQ f raw eta).upper := funext fun j => (hends j).2
    cases b
    dsimp only [compileBoxQ] at hl hu ⊢
    cases hs
    cases hl
    cases hu
    rfl
  · rintro rfl
    exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- The stronger negative statement is independent of any PSD factor payload. -/
theorem checked_no_identity_in_budget {p m q : ℕ} {model : ModelQ p m}
    (f : FamilyQ model q) (raw : Fin (q + 1) → ℚ) (eta : ℚ)
    (b : BoxQ (rowCount p m) (q + 1)) (hb : checkBoxQ f raw eta b = true)
    (w : RationalBoxSystem.ObstructionQ (rowCount p m) (q + 1))
    (hw : RationalBoxSystem.checkObstructionQ b w = true) :
    ¬ ∃ x,
      certificateRhsExprQ (instantiateQ f x) = upperTargetExprQ (x 0) f.objective ∧
      (∀ j : Fin q, 0 ≤ x j.succ) ∧ WithinBudgetQ raw x eta := by
  have he := (checkBoxQ_eq_true_iff f raw eta b).mp hb
  rintro ⟨x, hx, hn, hbudget⟩
  have hf : FeasibleQ (compileBoxQ f raw eta) x :=
    (feasible_iff f raw x eta).mpr ⟨(identity_iff_solution f x).mp hx, hn, hbudget⟩
  exact RationalBoxSystem.checked_obstruction b w hw ⟨x, he.symm ▸ hf⟩

/-- No accepted certificate in this fixed family within these raw-coordinate
budgets. The negative direction needs no assumption that the fixed matrix is PSD. -/
theorem checked_no_accepted_in_budget {p m q : ℕ} {model : ModelQ p m}
    (f : FamilyQ model q) (raw : Fin (q + 1) → ℚ) (eta : ℚ)
    (b : BoxQ (rowCount p m) (q + 1)) (hb : checkBoxQ f raw eta b = true)
    (w : RationalBoxSystem.ObstructionQ (rowCount p m) (q + 1))
    (hw : RationalBoxSystem.checkObstructionQ b w = true) :
    ¬ ∃ x, checkUpperCertQ (instantiateQ f x) = true ∧ WithinBudgetQ raw x eta := by
  have he := (checkBoxQ_eq_true_iff f raw eta b).mp hb
  rintro ⟨x, hx, hbudget⟩
  have hc := (accepted_iff f x).mp hx
  have hf : FeasibleQ (compileBoxQ f raw eta) x :=
    (feasible_iff f raw x eta).mpr ⟨hc.1, hc.2.1, hbudget⟩
  exact RationalBoxSystem.checked_obstruction b w hw ⟨x, he.symm ▸ hf⟩

/-- Bind raw coordinates without a default read or an unchecked positional cast.
The vector includes bound and all raw weights; the complete reference list must
also agree with the seed family. This is an independent gate, not JSON provenance. -/
def checkRawVectorQ {p m : ℕ} {model : ModelQ p m} (seed raw : UpperCertQ model)
    (v : Fin (seed.assumptionTerms.length + 1) → ℚ) : Bool :=
  decide (seed.assumptionTerms.map (fun t => t.index.val) =
    raw.assumptionTerms.map (fun t => t.index.val)) &&
  decide (List.ofFn v = raw.bound :: raw.assumptionTerms.map (fun t => t.weight))

theorem checkRawVectorQ_eq_true_iff {p m : ℕ} {model : ModelQ p m}
    (seed raw : UpperCertQ model) (v : Fin (seed.assumptionTerms.length + 1) → ℚ) :
    checkRawVectorQ seed raw v = true ↔
      seed.assumptionTerms.map (fun t => t.index.val) =
        raw.assumptionTerms.map (fun t => t.index.val) ∧
      List.ofFn v = raw.bound :: raw.assumptionTerms.map (fun t => t.weight) := by
  simp [checkRawVectorQ]

end LeanPEP.GramPEP.UpperCoefficientBox
