import LeanPEP.GramPEP.UpperCertificate
import Mathlib.Algebra.BigOperators.Fin

/-!
# Proof-only additive bookkeeping for exact expression coefficients

`coefficients` only packages the THREE EXISTING fields of `LinearExprQ`.
Its injectivity is proved below. No new polynomial semantics or checker is
introduced. The product's existing rational-module operations allow ordinary
finite sums without adding global algebra instances to `LinearExprQ`.
-/

namespace LeanPEP.GramPEP.CoefficientAlgebra

open scoped BigOperators

abbrev CoefficientsQ (p m : ℕ) := ℚ × ((Fin p → ℚ) × Gram m ℚ)

def coefficients {p m : ℕ} (e : LinearExprQ p m) : CoefficientsQ p m :=
  (e.constCoeff, (e.valueCoeff, e.gramCoeff))

theorem coefficients_injective {p m : ℕ} :
    Function.Injective (coefficients (p := p) (m := m)) := by
  intro a b h
  apply LinearExprQ.ext
  · exact congrArg Prod.fst h
  · exact congrArg (fun e : CoefficientsQ p m => e.2.1) h
  · exact congrArg (fun e : CoefficientsQ p m => e.2.2) h

theorem coeff_ext {p m : ℕ} {a b : CoefficientsQ p m}
    (hc : a.1 = b.1) (hv : ∀ i, a.2.1 i = b.2.1 i)
    (hg : ∀ i j, a.2.2 i j = b.2.2 i j) : a = b := by
  exact Prod.ext hc (Prod.ext (funext hv) (funext fun i => funext (hg i)))

@[simp] theorem coefficients_zero (p m : ℕ) :
    coefficients (LinearExprQ.zero p m) = 0 := rfl
@[simp] theorem coefficients_add {p m : ℕ} (a b : LinearExprQ p m) :
    coefficients (LinearExprQ.add a b) = coefficients a + coefficients b := rfl
@[simp] theorem coefficients_neg {p m : ℕ} (a : LinearExprQ p m) :
    coefficients (LinearExprQ.neg a) = -coefficients a := rfl
@[simp] theorem coefficients_sub {p m : ℕ} (a b : LinearExprQ p m) :
    coefficients (LinearExprQ.sub a b) = coefficients a - coefficients b := by
  simp only [LinearExprQ.sub, coefficients_add, coefficients_neg, sub_eq_add_neg]
@[simp] theorem coefficients_scale {p m : ℕ} (r : ℚ) (a : LinearExprQ p m) :
    coefficients (LinearExprQ.scale r a) = r • coefficients a := by
  apply coeff_ext <;> intros <;> simp [coefficients, LinearExprQ.scale, smul_eq_mul]

/-- Exact symmetric coefficient bilinear form, not a numeric Gram evaluation. -/
def bilinear {p m : ℕ} (u v : VecExpr m ℚ) : CoefficientsQ p m :=
  coefficients (LinearExprQ.gramBilinear u v)

def normSquare {p m : ℕ} (u : VecExpr m ℚ) : CoefficientsQ p m := bilinear u u

@[simp] theorem coefficients_gramBilinear {p m : ℕ} (u v : VecExpr m ℚ) :
    coefficients (LinearExprQ.gramBilinear (p := p) u v) = bilinear u v := rfl
@[simp] theorem coefficients_gramNorm {p m : ℕ} (u : VecExpr m ℚ) :
    coefficients (LinearExprQ.gramNorm (p := p) u) = normSquare u := rfl

theorem bilinear_comm {p m : ℕ} (u v : VecExpr m ℚ) :
    bilinear (p := p) u v = bilinear v u := by
  apply coeff_ext <;> intros <;>
    dsimp [bilinear, coefficients, LinearExprQ.gramBilinear, LinearExprQ.scale,
      LinearExprQ.add, LinearExprQ.gramOuter] <;> ring

@[simp] theorem bilinear_zero_left {p m : ℕ} (v : VecExpr m ℚ) :
    bilinear (p := p) 0 v = 0 := by
  apply coeff_ext <;> intros <;>
    simp [bilinear, coefficients, LinearExprQ.gramBilinear, LinearExprQ.scale,
      LinearExprQ.add, LinearExprQ.gramOuter]
@[simp] theorem bilinear_zero_right {p m : ℕ} (v : VecExpr m ℚ) :
    bilinear (p := p) v 0 = 0 := by rw [bilinear_comm, bilinear_zero_left]

@[simp] theorem bilinear_sub_left {p m : ℕ} (u v w : VecExpr m ℚ) :
    bilinear (p := p) (u - v) w = bilinear u w - bilinear v w := by
  apply coeff_ext <;> intros <;>
    dsimp [bilinear, coefficients, LinearExprQ.gramBilinear, LinearExprQ.scale,
      LinearExprQ.add, LinearExprQ.gramOuter] <;> ring
@[simp] theorem bilinear_sub_right {p m : ℕ} (u v w : VecExpr m ℚ) :
    bilinear (p := p) u (v - w) = bilinear u v - bilinear u w := by
  rw [bilinear_comm u (v - w), bilinear_sub_left,
    bilinear_comm v u, bilinear_comm w u]
@[simp] theorem bilinear_neg_left {p m : ℕ} (u v : VecExpr m ℚ) :
    bilinear (p := p) (-u) v = -bilinear u v := by
  simpa only [zero_sub, bilinear_zero_left] using bilinear_sub_left (p := p) 0 u v
@[simp] theorem bilinear_neg_right {p m : ℕ} (u v : VecExpr m ℚ) :
    bilinear (p := p) u (-v) = -bilinear u v := by
  rw [bilinear_comm, bilinear_neg_left, bilinear_comm]

theorem normSquare_sub_comm {p m : ℕ} (u v : VecExpr m ℚ) :
    normSquare (p := p) (u - v) = normSquare (v - u) := by
  simp only [normSquare, bilinear_sub_left, bilinear_sub_right]
  abel

/-- The original recursive assumption sum becomes an ordinary coefficient sum. -/
theorem coefficients_assumptionExprSumQ {p m : ℕ} (model : ModelQ p m)
    (terms : List (AssumptionTermQ model)) :
    coefficients (assumptionExprSumQ model terms) =
      (terms.map fun t => t.weight • coefficients (model.assumptions.get t.index)).sum := by
  induction terms with
  | nil => simp [assumptionExprSumQ]
  | cons t ts ih => simp only [assumptionExprSumQ, coefficients_add, coefficients_scale,
      List.map_cons, List.sum_cons, ih]

private theorem pairing_add {p m : ℕ} (A B : Gram m ℚ) :
    coefficients (LinearExprQ.gramPairing (p := p) (A + B)) =
      coefficients (LinearExprQ.gramPairing A) + coefficients (LinearExprQ.gramPairing B) := by
  apply coeff_ext <;> intros <;> simp [coefficients, LinearExprQ.gramPairing]

private theorem pairing_weightedOuterQ {p m : ℕ} (t : RankOneFactorQ m) :
    coefficients (LinearExprQ.gramPairing (p := p) (weightedOuterQ t)) =
      t.weight • normSquare t.vector := by
  apply coeff_ext <;> intros <;>
    dsimp [coefficients, normSquare, bilinear, LinearExprQ.gramPairing, weightedOuterQ,
      LinearExprQ.gramBilinear, LinearExprQ.scale, LinearExprQ.add, LinearExprQ.gramOuter] <;> ring

/-- Exact factor matrix reconstruction, keeping the original factor list. -/
theorem coefficients_factorGramQ {p m : ℕ} (terms : List (RankOneFactorQ m)) :
    coefficients (LinearExprQ.gramPairing (p := p) (factorGramQ terms)) =
      (terms.map fun t => t.weight • normSquare t.vector).sum := by
  induction terms with
  | nil =>
      apply coeff_ext <;> intros <;>
        simp [factorGramQ, coefficients, LinearExprQ.gramPairing]
  | cons t ts ih =>
      simp only [factorGramQ, pairing_add, pairing_weightedOuterQ,
        List.map_cons, List.sum_cons, ih]

end LeanPEP.GramPEP.CoefficientAlgebra
