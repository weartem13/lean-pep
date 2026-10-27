import LeanPEP.ActualFunction.AffineEvaluationCore
import LeanPEP.Toy.FiniteGD.ParametricUpperQuadraticDiagonal
import Mathlib.Tactic

/-!
# Hilbert-space semantics for the parameterized finite-GD certificate

The parameterized `FiniteGD` checker is implemented as an exact quadratic
polynomial identity in one scalar initial displacement, the sampled gradients,
and the sampled function values.  This file gives that same coefficient object
an exact interpretation in an arbitrary real inner-product space:

* the polynomial constant is paired with the squared norm of an initial
  displacement vector `u0`;
* a gradient-linear coefficient is paired with `⟪u0, g_i⟫`;
* an ordered gradient-quadratic coefficient is paired with `⟪g_i, g_j⟫`; and
* function-value coefficients retain their scalar meaning.

Under this interpretation, generated interpolation polynomials are the usual
Hilbert-space smooth-convex interpolation slacks, and generated affine squares
become actual squared norms.  Consequently the already kernel-verified
arbitrary-`N` certificate proves a universal upper bound for every abstract
Hilbert trajectory satisfying all generated interpolation inequalities.

This is still a semantic trajectory theorem.  It does not yet assert that the
trajectory comes from an actual smooth-convex function; that realization is a
separate next bridge.
-/

namespace LeanPEP
namespace ActualFunction
namespace ParametricGDHilbert

open scoped BigOperators
open Toy.FiniteGD
open Toy.FiniteGD.ParametricUpper

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pair rational coefficients with the initial-displacement/gradient cross
inner products. -/
noncomputable def crossInnerR
    {N : ℕ}
    (a : Fin (N + 1) → ℚ)
    (u0 : E)
    (grad : Fin (N + 1) → E) : ℝ :=
  ∑ i, (a i : ℝ) * inner ℝ u0 (grad i)

/-- Evaluate an ordered rational quadratic coefficient matrix on the actual
sampled-gradient Gram matrix. -/
noncomputable def quadraticInnerR
    {N : ℕ}
    (q : Fin (N + 1) → Fin (N + 1) → ℚ)
    (grad : Fin (N + 1) → E) : ℝ :=
  ∑ i, ∑ j, (q i j : ℝ) * inner ℝ (grad i) (grad j)

@[simp] theorem crossInnerR_zero
    {N : ℕ} (u0 : E) (grad : Fin (N + 1) → E) :
    crossInnerR (fun _ => 0) u0 grad = 0 := by
  simp [crossInnerR]

@[simp] theorem crossInnerR_add
    {N : ℕ}
    (a b : Fin (N + 1) → ℚ)
    (u0 : E) (grad : Fin (N + 1) → E) :
    crossInnerR (fun i => a i + b i) u0 grad =
      crossInnerR a u0 grad + crossInnerR b u0 grad := by
  simp [crossInnerR, add_mul, Finset.sum_add_distrib]

@[simp] theorem crossInnerR_neg
    {N : ℕ}
    (a : Fin (N + 1) → ℚ)
    (u0 : E) (grad : Fin (N + 1) → E) :
    crossInnerR (fun i => -a i) u0 grad =
      -crossInnerR a u0 grad := by
  simp [crossInnerR]

@[simp] theorem crossInnerR_scale
    {N : ℕ}
    (c : ℚ)
    (a : Fin (N + 1) → ℚ)
    (u0 : E) (grad : Fin (N + 1) → E) :
    crossInnerR (fun i => c * a i) u0 grad =
      (c : ℝ) * crossInnerR a u0 grad := by
  simp [crossInnerR, Finset.mul_sum, mul_assoc]

@[simp] theorem quadraticInnerR_zero
    {N : ℕ} (grad : Fin (N + 1) → E) :
    quadraticInnerR (fun _ _ => 0) grad = 0 := by
  simp [quadraticInnerR]

@[simp] theorem quadraticInnerR_add
    {N : ℕ}
    (q r : Fin (N + 1) → Fin (N + 1) → ℚ)
    (grad : Fin (N + 1) → E) :
    quadraticInnerR (fun i j => q i j + r i j) grad =
      quadraticInnerR q grad + quadraticInnerR r grad := by
  simp [quadraticInnerR, add_mul, Finset.sum_add_distrib]

@[simp] theorem quadraticInnerR_neg
    {N : ℕ}
    (q : Fin (N + 1) → Fin (N + 1) → ℚ)
    (grad : Fin (N + 1) → E) :
    quadraticInnerR (fun i j => -q i j) grad =
      -quadraticInnerR q grad := by
  simp [quadraticInnerR]

@[simp] theorem quadraticInnerR_scale
    {N : ℕ}
    (c : ℚ)
    (q : Fin (N + 1) → Fin (N + 1) → ℚ)
    (grad : Fin (N + 1) → E) :
    quadraticInnerR (fun i j => c * q i j) grad =
      (c : ℝ) * quadraticInnerR q grad := by
  simp [quadraticInnerR, Finset.mul_sum, mul_assoc]

/-- Prefix sum of actual sampled-gradient vectors. -/
noncomputable def prefixVector
    {N : ℕ}
    (grad : Fin (N + 1) → E) :
    (k : ℕ) → k ≤ N + 1 → E
  | 0, _ => 0
  | k + 1, hk =>
      prefixVector grad k (Nat.le_trans (Nat.le_succ k) hk) +
        grad ⟨k, Nat.lt_of_succ_le hk⟩

/-- Centered position attached to each generated finite-GD point. -/
noncomputable def pointPosition
    {N : ℕ}
    (u0 : E)
    (grad : Fin (N + 1) → E) : Point N → E
  | Point.star => 0
  | Point.iter k =>
      u0 - prefixVector grad k.val (Nat.le_of_lt k.isLt)

/-- Actual gradient vector attached to each generated finite-GD point. -/
def pointGradient
    {N : ℕ}
    (grad : Fin (N + 1) → E) : Point N → E
  | Point.star => 0
  | Point.iter k => grad k

/-- Centered function value attached to each generated finite-GD point. -/
def pointValue
    {N : ℕ}
    (value : Fin (N + 1) → ℝ) : Point N → ℝ
  | Point.star => 0
  | Point.iter k => value k

/-- The symbolic prefix affine form realizes the actual vector prefix. -/
theorem evalVector_prefixAffine
    {N : ℕ}
    (u0 : E) (grad : Fin (N + 1) → E) :
    ∀ (k : ℕ) (hk : k ≤ N + 1),
      evalVector (GradAffineQ.prefixAffine k hk) u0 grad =
        prefixVector grad k hk := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [GradAffineQ.prefixAffine, prefixVector]
  | succ k ih =>
      intro hk
      simp [GradAffineQ.prefixAffine, prefixVector, ih]

@[simp] theorem evalVector_xAffineQ
    {N : ℕ}
    (u0 : E) (grad : Fin (N + 1) → E)
    (i : Point N) :
    evalVector (xAffineQ i) u0 grad = pointPosition u0 grad i := by
  cases i with
  | star =>
      simp [xAffineQ, pointPosition]
  | iter k =>
      simp [xAffineQ, pointPosition, evalVector_prefixAffine]

@[simp] theorem evalVector_gradAffineQ
    {N : ℕ}
    (u0 : E) (grad : Fin (N + 1) → E)
    (i : Point N) :
    evalVector (gradAffineQ i) u0 grad = pointGradient grad i := by
  cases i <;> simp [gradAffineQ, pointGradient]

/-- Cross-inner evaluation is the inner product with the realized linear
combination. -/
theorem inner_linearCombination_right
    {N : ℕ}
    (a : Fin (N + 1) → ℚ)
    (u0 : E) (grad : Fin (N + 1) → E) :
    inner ℝ u0 (linearCombination a grad) =
      crossInnerR a u0 grad := by
  unfold linearCombination crossInnerR
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [real_inner_smul_right]

/-- Symmetric companion of `inner_linearCombination_right`. -/
theorem inner_linearCombination_left
    {N : ℕ}
    (a : Fin (N + 1) → ℚ)
    (u0 : E) (grad : Fin (N + 1) → E) :
    inner ℝ (linearCombination a grad) u0 =
      crossInnerR a u0 grad := by
  rw [real_inner_comm]
  exact inner_linearCombination_right a u0 grad

/-- Ordered outer-product coefficients evaluate to the ambient inner product
of the represented linear combinations. -/
theorem quadraticInnerR_outerQ
    {N : ℕ}
    (a b : Fin (N + 1) → ℚ)
    (grad : Fin (N + 1) → E) :
    quadraticInnerR (outerQ a b) grad =
      inner ℝ (linearCombination a grad) (linearCombination b grad) := by
  calc
    quadraticInnerR (outerQ a b) grad =
        ∑ i, ∑ j,
          inner ℝ ((a i : ℝ) • grad i) ((b j : ℝ) • grad j) := by
      unfold quadraticInnerR outerQ
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [real_inner_smul_left, real_inner_smul_right]
      simp only [Rat.cast_mul]
      ring
    _ = inner ℝ (∑ i, (a i : ℝ) • grad i)
          (∑ j, (b j : ℝ) • grad j) := by
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [inner_sum]
    _ = inner ℝ (linearCombination a grad)
          (linearCombination b grad) := rfl

/-- Symmetrized outer-product coefficients have the same Hilbert semantics as
one ordered outer product because the ambient Gram matrix is symmetric. -/
theorem quadraticInnerR_symOuterQ
    {N : ℕ}
    (a b : Fin (N + 1) → ℚ)
    (grad : Fin (N + 1) → E) :
    quadraticInnerR (symOuterQ a b) grad =
      inner ℝ (linearCombination a grad) (linearCombination b grad) := by
  have hrewrite :
      symOuterQ a b =
        fun i j => ((1 : ℚ) / 2) *
          (outerQ a b i j + outerQ b a i j) := by
    funext i j
    simp [symOuterQ, outerQ] <;> ring
  rw [hrewrite, quadraticInnerR_scale, quadraticInnerR_add,
    quadraticInnerR_outerQ, quadraticInnerR_outerQ]
  rw [real_inner_comm (linearCombination b grad)
    (linearCombination a grad)]
  ring

/-- Exact Hilbert-space interpretation of one quadratic coefficient object. -/
noncomputable def evalHilbert
    {N : ℕ}
    (p : QuadPolyQ N)
    (u0 : E)
    (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ) : ℝ :=
  (p.constCoeff : ℝ) * inner ℝ u0 u0
    + crossInnerR p.gradCoeff u0 grad
    + dotR p.valueCoeff value
    + quadraticInnerR p.quadCoeff grad

@[simp] theorem evalHilbert_zero
    {N : ℕ}
    (u0 : E) (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ) :
    evalHilbert (QuadPolyQ.zero N) u0 grad value = 0 := by
  simp [evalHilbert, QuadPolyQ.zero]

@[simp] theorem evalHilbert_add
    {N : ℕ}
    (p q : QuadPolyQ N)
    (u0 : E) (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ) :
    evalHilbert (QuadPolyQ.add p q) u0 grad value =
      evalHilbert p u0 grad value + evalHilbert q u0 grad value := by
  simp [evalHilbert, QuadPolyQ.add, add_mul] <;> ring

@[simp] theorem evalHilbert_neg
    {N : ℕ}
    (p : QuadPolyQ N)
    (u0 : E) (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ) :
    evalHilbert (QuadPolyQ.neg p) u0 grad value =
      -evalHilbert p u0 grad value := by
  simp [evalHilbert, QuadPolyQ.neg] <;> ring

@[simp] theorem evalHilbert_sub
    {N : ℕ}
    (p q : QuadPolyQ N)
    (u0 : E) (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ) :
    evalHilbert (QuadPolyQ.sub p q) u0 grad value =
      evalHilbert p u0 grad value - evalHilbert q u0 grad value := by
  simp [QuadPolyQ.sub] <;> ring

@[simp] theorem evalHilbert_scale
    {N : ℕ}
    (c : ℚ) (p : QuadPolyQ N)
    (u0 : E) (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ) :
    evalHilbert (QuadPolyQ.scale c p) u0 grad value =
      (c : ℝ) * evalHilbert p u0 grad value := by
  simp [evalHilbert, QuadPolyQ.scale] <;> ring

@[simp] theorem evalHilbert_valueVar
    {N : ℕ}
    (i : Fin (N + 1))
    (u0 : E) (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ) :
    evalHilbert (QuadPolyQ.valueVar i) u0 grad value = value i := by
  simp [evalHilbert, QuadPolyQ.valueVar]

/-- Hilbert evaluation of a product of affine gradient forms is the actual
ambient inner product of the two represented vectors. -/
@[simp] theorem evalHilbert_mulAffine
    {N : ℕ}
    (a b : GradAffineQ N)
    (u0 : E) (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ) :
    evalHilbert (QuadPolyQ.mulAffine a b) u0 grad value =
      inner ℝ (evalVector a u0 grad) (evalVector b u0 grad) := by
  calc
    evalHilbert (QuadPolyQ.mulAffine a b) u0 grad value =
        ((a.constCoeff : ℝ) * (b.constCoeff : ℝ)) * inner ℝ u0 u0
          + (a.constCoeff : ℝ) * crossInnerR b.gradCoeff u0 grad
          + (b.constCoeff : ℝ) * crossInnerR a.gradCoeff u0 grad
          + inner ℝ (linearCombination a.gradCoeff grad)
              (linearCombination b.gradCoeff grad) := by
      simp only [evalHilbert, QuadPolyQ.mulAffine, Rat.cast_mul,
        crossInnerR_add, crossInnerR_scale, dotR_zero,
        quadraticInnerR_symOuterQ, add_zero]
      ring
    _ = inner ℝ (evalVector a u0 grad) (evalVector b u0 grad) := by
      unfold evalVector
      simp only [inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [inner_linearCombination_right b.gradCoeff u0 grad,
        inner_linearCombination_left a.gradCoeff u0 grad]
      ring

@[simp] theorem evalHilbert_square
    {N : ℕ}
    (a : GradAffineQ N)
    (u0 : E) (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ) :
    evalHilbert (QuadPolyQ.square a) u0 grad value =
      inner ℝ (evalVector a u0 grad) (evalVector a u0 grad) := by
  simp [QuadPolyQ.square, evalHilbert_mulAffine]

@[simp] theorem evalHilbert_pointValuePolyQ
    {N : ℕ}
    (u0 : E) (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ)
    (i : Point N) :
    evalHilbert (pointValuePolyQ i) u0 grad value = pointValue value i := by
  cases i <;> simp [pointValuePolyQ, pointValue]

/-- Hilbert-space interpolation slack for the generated centered trajectory. -/
noncomputable def interpolationSlack
    {N : ℕ}
    (u0 : E)
    (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ)
    (i j : Point N) : ℝ :=
  pointValue value i - pointValue value j
    - inner ℝ (pointGradient grad j)
        (pointPosition u0 grad i - pointPosition u0 grad j)
    - ((1 : ℝ) / 2) *
        inner ℝ
          (pointGradient grad i - pointGradient grad j)
          (pointGradient grad i - pointGradient grad j)

/-- The executable slack polynomial has the exact generated Hilbert-space
interpolation semantics. -/
@[simp] theorem evalHilbert_slackPolyQ
    {N : ℕ}
    (u0 : E)
    (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ)
    (i j : Point N) :
    evalHilbert (slackPolyQ i j) u0 grad value =
      interpolationSlack u0 grad value i j := by
  simp [slackPolyQ, interpolationSlack, evalHilbert_mulAffine] <;> ring

/-- All generated ordered interpolation inequalities hold for one abstract
Hilbert trajectory. -/
def Feasible
    {N : ℕ}
    (u0 : E)
    (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ) : Prop :=
  ∀ i j : Point N, 0 ≤ interpolationSlack u0 grad value i j

/-- Hilbert value of all weighted interpolation terms. -/
noncomputable def interpTermsValue
    {N : ℕ}
    (u0 : E)
    (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ) :
    List (InterpTermQ N) → ℝ
  | [] => 0
  | t :: ts =>
      (t.weight : ℝ) * interpolationSlack u0 grad value t.i t.j +
        interpTermsValue u0 grad value ts

/-- Hilbert value of all weighted squared ambient norms. -/
noncomputable def squareTermsValue
    {N : ℕ}
    (u0 : E)
    (grad : Fin (N + 1) → E) :
    List (SquareTermQ N) → ℝ
  | [] => 0
  | t :: ts =>
      (t.weight : ℝ) *
          inner ℝ (evalVector t.form u0 grad) (evalVector t.form u0 grad) +
        squareTermsValue u0 grad ts

@[simp] theorem evalHilbert_interpPolySumQ
    {N : ℕ}
    (u0 : E)
    (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ)
    (terms : List (InterpTermQ N)) :
    evalHilbert (interpPolySumQ terms) u0 grad value =
      interpTermsValue u0 grad value terms := by
  induction terms with
  | nil =>
      simp [interpPolySumQ, interpTermsValue]
  | cons t ts ih =>
      simp [interpPolySumQ, interpTermsValue, ih]

@[simp] theorem evalHilbert_squarePolySumQ
    {N : ℕ}
    (u0 : E)
    (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ)
    (terms : List (SquareTermQ N)) :
    evalHilbert (squarePolySumQ terms) u0 grad value =
      squareTermsValue u0 grad terms := by
  induction terms with
  | nil =>
      simp [squarePolySumQ, squareTermsValue]
  | cons t ts ih =>
      simp [squarePolySumQ, squareTermsValue, ih]

@[simp] theorem evalHilbert_certificateRhsPolyQ
    {N : ℕ}
    (u0 : E)
    (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ)
    (c : UpperCertQ N) :
    evalHilbert (certificateRhsPolyQ c) u0 grad value =
      interpTermsValue u0 grad value c.interpTerms +
        squareTermsValue u0 grad c.squareTerms := by
  simp [certificateRhsPolyQ]

@[simp] theorem evalHilbert_upperTargetPolyQ
    {N : ℕ}
    (u0 : E)
    (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ)
    (bound : ℚ)
    (objective : Fin (N + 1)) :
    evalHilbert (upperTargetPolyQ bound objective) u0 grad value =
      (bound : ℝ) * inner ℝ u0 u0 - value objective := by
  unfold upperTargetPolyQ
  rw [evalHilbert_sub, evalHilbert_valueVar]
  simp only [evalHilbert, QuadPolyQ.ofAffine, GradAffineQ.const,
    crossInnerR_zero, dotR_zero, quadraticInnerR_zero, add_zero]

/-- Nonnegative interpolation weights preserve abstract Hilbert feasibility. -/
theorem interpTermsValue_nonneg
    {N : ℕ}
    (u0 : E)
    (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ)
    (hfeasible : Feasible u0 grad value)
    (terms : List (InterpTermQ N))
    (hweights : ∀ t ∈ terms, 0 ≤ t.weight) :
    0 ≤ interpTermsValue u0 grad value terms := by
  revert hweights
  induction terms with
  | nil =>
      intro hweights
      simp [interpTermsValue]
  | cons t ts ih =>
      intro hweights
      have hweightQ : 0 ≤ t.weight := hweights t (by simp)
      have hweightR : 0 ≤ (t.weight : ℝ) := Rat.cast_nonneg.mpr hweightQ
      have hslack : 0 ≤ interpolationSlack u0 grad value t.i t.j :=
        hfeasible t.i t.j
      have htailWeights : ∀ u ∈ ts, 0 ≤ u.weight := by
        intro u hu
        exact hweights u (by simp [hu])
      have htail : 0 ≤ interpTermsValue u0 grad value ts :=
        ih htailWeights
      simp only [interpTermsValue]
      exact add_nonneg (mul_nonneg hweightR hslack) htail

/-- Nonnegative square weights preserve nonnegativity of actual squared
ambient norms. -/
theorem squareTermsValue_nonneg
    {N : ℕ}
    (u0 : E)
    (grad : Fin (N + 1) → E)
    (terms : List (SquareTermQ N))
    (hweights : ∀ t ∈ terms, 0 ≤ t.weight) :
    0 ≤ squareTermsValue u0 grad terms := by
  revert hweights
  induction terms with
  | nil =>
      intro hweights
      simp [squareTermsValue]
  | cons t ts ih =>
      intro hweights
      have hweightQ : 0 ≤ t.weight := hweights t (by simp)
      have hweightR : 0 ≤ (t.weight : ℝ) := Rat.cast_nonneg.mpr hweightQ
      have hsquare :
          0 ≤ inner ℝ (evalVector t.form u0 grad)
            (evalVector t.form u0 grad) :=
        real_inner_self_nonneg
      have htailWeights : ∀ u ∈ ts, 0 ≤ u.weight := by
        intro u hu
        exact hweights u (by simp [hu])
      have htail : 0 ≤ squareTermsValue u0 grad ts := ih htailWeights
      simp only [squareTermsValue]
      exact add_nonneg (mul_nonneg hweightR hsquare) htail

/-- Every propositionally valid scalar coefficient certificate is sound under
its exact arbitrary-Hilbert interpretation. -/
theorem upperCertValidQ_sound
    {N : ℕ}
    (c : UpperCertQ N)
    (hc : UpperCertValidQ c)
    (u0 : E)
    (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ)
    (hfeasible : Feasible u0 grad value) :
    value c.objective ≤ (c.bound : ℝ) * inner ℝ u0 u0 := by
  have hinterp :
      0 ≤ interpTermsValue u0 grad value c.interpTerms :=
    interpTermsValue_nonneg u0 grad value hfeasible
      c.interpTerms hc.interpWeights
  have hsquares :
      0 ≤ squareTermsValue u0 grad c.squareTerms :=
    squareTermsValue_nonneg u0 grad c.squareTerms hc.squareWeights
  have htotal :
      0 ≤ interpTermsValue u0 grad value c.interpTerms +
        squareTermsValue u0 grad c.squareTerms :=
    add_nonneg hinterp hsquares
  have hidentity :
      (c.bound : ℝ) * inner ℝ u0 u0 - value c.objective =
        interpTermsValue u0 grad value c.interpTerms +
          squareTermsValue u0 grad c.squareTerms := by
    have heval := congrArg
      (fun p : QuadPolyQ N => evalHilbert p u0 grad value)
      hc.identity
    simpa using heval.symm
  nlinarith

/-- The kernel-verified generated arbitrary-`N` certificate proves the exact
Hilbert-trajectory upper bound. -/
theorem gd_upper
    (N : ℕ)
    (u0 : E)
    (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ)
    (hfeasible : Feasible u0 grad value) :
    value (gdObjective N) ≤
      (gdBoundQ N : ℝ) * inner ℝ u0 u0 := by
  exact upperCertValidQ_sound
    (gdUpperCertQ N)
    (checkUpperCertQ_sound
      (gdUpperCertQ N) (gdUpperCertQ_check_all N))
    u0 grad value hfeasible

/-- Norm-squared form of the abstract arbitrary-Hilbert trajectory theorem. -/
theorem gd_upper_normSq
    (N : ℕ)
    (u0 : E)
    (grad : Fin (N + 1) → E)
    (value : Fin (N + 1) → ℝ)
    (hfeasible : Feasible u0 grad value) :
    value (gdObjective N) ≤
      (gdBoundQ N : ℝ) * ‖u0‖ ^ 2 := by
  simpa [real_inner_self_eq_norm_sq] using
    gd_upper N u0 grad value hfeasible

end ParametricGDHilbert
end ActualFunction
end LeanPEP
