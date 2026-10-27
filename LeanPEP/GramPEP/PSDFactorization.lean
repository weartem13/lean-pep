import LeanPEP.GramPEP.Core

/-!
# Exact rational PSD factorization certificates

A Gram matrix is positive semidefinite when it is a nonnegative weighted sum
of rational rank-one matrices.  This module makes that statement executable:

* every factor weight is checked with exact rational arithmetic;
* symmetry of the target Gram matrix is checked entry by entry;
* the factorized matrix is compared with the target entry by entry; and
* a soundness theorem converts Boolean acceptance into
  `GramPEP.IsGramPosSemidef`.

No eigenvalue computation or floating-point tolerance is used.  The vector
dimension is carried by `Fin m`, so malformed factor-vector lengths are not
representable in this typed Lean layer.  A later external-artifact importer
will diagnose source-level length mismatches before constructing these terms.
-/

namespace LeanPEP
namespace GramPEP

open scoped BigOperators

/-- Every Gram coordinate `0, ..., m - 1`. -/
def gramIndices (m : ℕ) : List (Fin m) :=
  List.finRange m

/-- Every ordered Gram-matrix entry in row-major order. -/
def gramIndexPairs (m : ℕ) : List (Fin m × Fin m) :=
  (gramIndices m).flatMap (fun i =>
    (gramIndices m).map (fun j => (i, j)))

@[simp] theorem mem_gramIndices {m : ℕ} (i : Fin m) :
    i ∈ gramIndices m := by
  simp [gramIndices]

@[simp] theorem mem_gramIndexPairs {m : ℕ} (i j : Fin m) :
    (i, j) ∈ gramIndexPairs m := by
  simp [gramIndexPairs]

/-- Exact rational dot product of two coefficient vectors. -/
def vecDotQ {m : ℕ} (u v : VecExpr m ℚ) : ℚ :=
  ∑ i, u i * v i

/-- One nonnegative weighted rank-one factor `weight * vector * vectorᵀ`. -/
structure RankOneFactorQ (m : ℕ) where
  weight : ℚ
  vector : VecExpr m ℚ

/-- A rational PSD certificate represented by weighted rank-one factors. -/
structure PSDFactorCertQ (m : ℕ) where
  factors : List (RankOneFactorQ m)

/-- Matrix represented by one weighted rank-one factor. -/
def weightedOuterQ {m : ℕ} (t : RankOneFactorQ m) : Gram m ℚ :=
  fun i j => t.weight * t.vector i * t.vector j

/-- Matrix reconstructed from every rank-one factor. -/
def factorGramQ {m : ℕ} : List (RankOneFactorQ m) → Gram m ℚ
  | [] => 0
  | t :: ts => weightedOuterQ t + factorGramQ ts

/-- The zero Gram matrix represents the zero bilinear form. -/
@[simp] theorem gramInner_zero_gram
    {m : ℕ} (u v : VecExpr m ℚ) :
    gramInner (0 : Gram m ℚ) u v = 0 := by
  simp [gramInner]

/-- The zero Gram matrix has zero represented squared norm. -/
@[simp] theorem gramNormSq_zero_gram
    {m : ℕ} (u : VecExpr m ℚ) :
    gramNormSq (0 : Gram m ℚ) u = 0 := by
  simp [gramNormSq]

/-- Gram bilinear evaluation is additive in the matrix argument. -/
@[simp] theorem gramInner_add_gram
    {m : ℕ} (G H : Gram m ℚ) (u v : VecExpr m ℚ) :
    gramInner (G + H) u v = gramInner G u v + gramInner H u v := by
  simp [gramInner, mul_add, Finset.sum_add_distrib, add_mul]

/-- Gram squared norm is additive in the matrix argument. -/
@[simp] theorem gramNormSq_add_gram
    {m : ℕ} (G H : Gram m ℚ) (u : VecExpr m ℚ) :
    gramNormSq (G + H) u = gramNormSq G u + gramNormSq H u := by
  simp [gramNormSq]

/-- A weighted rank-one Gram term evaluates to one weighted exact square. -/
theorem gramNormSq_weightedOuterQ
    {m : ℕ} (t : RankOneFactorQ m) (u : VecExpr m ℚ) :
    gramNormSq (weightedOuterQ t) u =
      t.weight * (vecDotQ u t.vector)^2 := by
  calc
    gramNormSq (weightedOuterQ t) u =
        ∑ i, (t.weight * u i * t.vector i) *
          (∑ j, u j * t.vector j) := by
      unfold gramNormSq gramInner weightedOuterQ
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ i, t.weight * u i * t.vector i) *
          (∑ j, u j * t.vector j) := by
      rw [Finset.sum_mul]
    _ = t.weight * (∑ i, u i * t.vector i) *
          (∑ j, u j * t.vector j) := by
      have hfactor :
          (∑ i, t.weight * u i * t.vector i) =
            t.weight * (∑ i, u i * t.vector i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hfactor]
    _ = t.weight * (vecDotQ u t.vector)^2 := by
      simp [vecDotQ, pow_two, mul_assoc]

/-- The reconstructed factor matrix is symmetric, independently of weights. -/
theorem factorGramQ_symmetric
    {m : ℕ} (factors : List (RankOneFactorQ m)) :
    IsGramSymmetric (factorGramQ factors) := by
  intro i j
  induction factors with
  | nil =>
      rfl
  | cons t ts ih =>
      change
        t.weight * t.vector i * t.vector j + factorGramQ ts i j =
          t.weight * t.vector j * t.vector i + factorGramQ ts j i
      rw [ih]
      ring

/-- Nonnegative factor weights imply a nonnegative represented quadratic form. -/
theorem factorGramQ_norm_nonneg
    {m : ℕ}
    (factors : List (RankOneFactorQ m))
    (hweights : ∀ t ∈ factors, 0 ≤ t.weight)
    (u : VecExpr m ℚ) :
    0 ≤ gramNormSq (factorGramQ factors) u := by
  revert hweights
  induction factors with
  | nil =>
      intro hweights
      simp [factorGramQ]
  | cons t ts ih =>
      intro hweights
      have hweight : 0 ≤ t.weight := hweights t (by simp)
      have hrest : ∀ s ∈ ts, 0 ≤ s.weight := by
        intro s hs
        exact hweights s (by simp [hs])
      simp only [factorGramQ, gramNormSq_add_gram,
        gramNormSq_weightedOuterQ]
      exact add_nonneg
        (mul_nonneg hweight (sq_nonneg (vecDotQ u t.vector)))
        (ih hrest)

/-- A factorized matrix with nonnegative weights is propositionally PSD. -/
theorem factorGramQ_posSemidef
    {m : ℕ}
    (factors : List (RankOneFactorQ m))
    (hweights : ∀ t ∈ factors, 0 ≤ t.weight) :
    IsGramPosSemidef (factorGramQ factors) := by
  exact ⟨factorGramQ_symmetric factors,
    factorGramQ_norm_nonneg factors hweights⟩

/-- Exact entry-by-entry equality checker for rational Gram matrices. -/
def checkGramEqQ {m : ℕ} (G H : Gram m ℚ) : Bool :=
  (gramIndexPairs m).all (fun ij =>
    decide (G ij.1 ij.2 = H ij.1 ij.2))

/-- The entry checker exactly decides matrix equality. -/
theorem checkGramEqQ_eq_true_iff
    {m : ℕ} (G H : Gram m ℚ) :
    checkGramEqQ G H = true ↔ G = H := by
  unfold checkGramEqQ
  rw [List.all_eq_true]
  constructor
  · intro hall
    funext i j
    exact of_decide_eq_true
      (hall (i, j) (mem_gramIndexPairs i j))
  · intro h pair hpair
    rcases pair with ⟨i, j⟩
    subst H
    exact decide_eq_true rfl

/-- Exact symmetry checker for a rational Gram matrix. -/
def checkGramSymmetricQ {m : ℕ} (G : Gram m ℚ) : Bool :=
  (gramIndexPairs m).all (fun ij =>
    decide (G ij.1 ij.2 = G ij.2 ij.1))

/-- The executable symmetry checker exactly decides `IsGramSymmetric`. -/
theorem checkGramSymmetricQ_eq_true_iff
    {m : ℕ} (G : Gram m ℚ) :
    checkGramSymmetricQ G = true ↔ IsGramSymmetric G := by
  unfold checkGramSymmetricQ IsGramSymmetric
  rw [List.all_eq_true]
  constructor
  · intro hall i j
    exact of_decide_eq_true
      (hall (i, j) (mem_gramIndexPairs i j))
  · intro h pair hpair
    rcases pair with ⟨i, j⟩
    exact decide_eq_true (h i j)

/-- Exact nonnegative-weight checker. -/
def checkFactorWeightsQ {m : ℕ} (c : PSDFactorCertQ m) : Bool :=
  c.factors.all (fun t => decide (0 ≤ t.weight))

/-- The weight checker exactly decides nonnegativity of every factor weight. -/
theorem checkFactorWeightsQ_eq_true_iff
    {m : ℕ} (c : PSDFactorCertQ m) :
    checkFactorWeightsQ c = true ↔
      ∀ t ∈ c.factors, 0 ≤ t.weight := by
  simp [checkFactorWeightsQ, List.all_eq_true]

/-- Proposition-level meaning of a valid exact rational PSD certificate. -/
structure PSDFactorValidQ {m : ℕ}
    (G : Gram m ℚ) (c : PSDFactorCertQ m) : Prop where
  symmetric : IsGramSymmetric G
  weights : ∀ t ∈ c.factors, 0 ≤ t.weight
  identity : factorGramQ c.factors = G

/-- Check target symmetry, factor weights, and every factorization entry. -/
def checkPSDFactorQ {m : ℕ}
    (G : Gram m ℚ) (c : PSDFactorCertQ m) : Bool :=
  checkGramSymmetricQ G &&
    (checkFactorWeightsQ c &&
      checkGramEqQ (factorGramQ c.factors) G)

/-- Boolean acceptance exactly matches proposition-level certificate validity. -/
theorem checkPSDFactorQ_eq_true_iff
    {m : ℕ} (G : Gram m ℚ) (c : PSDFactorCertQ m) :
    checkPSDFactorQ G c = true ↔ PSDFactorValidQ G c := by
  constructor
  · intro h
    have hparts :
        checkGramSymmetricQ G = true ∧
        checkFactorWeightsQ c = true ∧
        checkGramEqQ (factorGramQ c.factors) G = true := by
      simpa [checkPSDFactorQ] using h
    exact
      { symmetric := (checkGramSymmetricQ_eq_true_iff G).mp hparts.1
        weights := (checkFactorWeightsQ_eq_true_iff c).mp hparts.2.1
        identity := (checkGramEqQ_eq_true_iff _ _).mp hparts.2.2 }
  · intro h
    have hsym := (checkGramSymmetricQ_eq_true_iff G).mpr h.symmetric
    have hweights := (checkFactorWeightsQ_eq_true_iff c).mpr h.weights
    have hid := (checkGramEqQ_eq_true_iff _ _).mpr h.identity
    simp [checkPSDFactorQ, hsym, hweights, hid]

/-- A valid factor certificate proves the target Gram matrix PSD. -/
theorem psdFactorValidQ_sound
    {m : ℕ} (G : Gram m ℚ) (c : PSDFactorCertQ m)
    (h : PSDFactorValidQ G c) :
    IsGramPosSemidef G := by
  rw [← h.identity]
  exact factorGramQ_posSemidef c.factors h.weights

/-- An accepted exact rational factor certificate proves PSD. -/
theorem checkPSDFactorQ_sound
    {m : ℕ} (G : Gram m ℚ) (c : PSDFactorCertQ m)
    (h : checkPSDFactorQ G c = true) :
    IsGramPosSemidef G :=
  psdFactorValidQ_sound G c ((checkPSDFactorQ_eq_true_iff G c).mp h)

/-- One exact asymmetry in the target matrix. -/
structure GramAsymmetryQ (m : ℕ) where
  i : Fin m
  j : Fin m
  left : ℚ
  right : ℚ
  deriving DecidableEq, Repr

/-- One negative factor weight, located by list index. -/
structure NegativeFactorWeightQ where
  index : Nat
  weight : ℚ
  deriving DecidableEq, Repr

/-- One exact target/factorized entry mismatch. -/
structure GramEntryMismatchQ (m : ℕ) where
  i : Fin m
  j : Fin m
  expected : ℚ
  actual : ℚ
  deriving DecidableEq, Repr

/-- Complete deterministic symmetry mismatch report. -/
def gramAsymmetriesQ {m : ℕ} (G : Gram m ℚ) :
    List (GramAsymmetryQ m) :=
  (gramIndexPairs m).flatMap (fun ij =>
    let left := G ij.1 ij.2
    let right := G ij.2 ij.1
    if left = right then [] else
      [{ i := ij.1, j := ij.2, left := left, right := right }])

/-- Scan factor weights while retaining their deterministic list indices. -/
def negativeFactorWeightsFromQ {m : ℕ} :
    Nat → List (RankOneFactorQ m) → List NegativeFactorWeightQ
  | _, [] => []
  | k, t :: ts =>
      let rest := negativeFactorWeightsFromQ (k + 1) ts
      if t.weight < 0 then
        { index := k, weight := t.weight } :: rest
      else
        rest

/-- Complete negative-weight report. -/
def negativeFactorWeightsQ {m : ℕ} (c : PSDFactorCertQ m) :
    List NegativeFactorWeightQ :=
  negativeFactorWeightsFromQ 0 c.factors

/-- Complete exact factorization-entry mismatch report. -/
def gramEntryMismatchesQ {m : ℕ}
    (G actual : Gram m ℚ) : List (GramEntryMismatchQ m) :=
  (gramIndexPairs m).flatMap (fun ij =>
    let expected := G ij.1 ij.2
    let found := actual ij.1 ij.2
    if expected = found then [] else
      [{ i := ij.1, j := ij.2,
         expected := expected, actual := found }])

/-- Structured exact PSD-factorization audit report. -/
structure PSDFactorAuditReportQ (m : ℕ) where
  accepted : Bool
  asymmetries : List (GramAsymmetryQ m)
  negativeWeights : List NegativeFactorWeightQ
  entryMismatches : List (GramEntryMismatchQ m)
  deriving DecidableEq, Repr

/-- Audit one target matrix and exact rational factor certificate. -/
def auditPSDFactorQ {m : ℕ}
    (G : Gram m ℚ) (c : PSDFactorCertQ m) :
    PSDFactorAuditReportQ m :=
  { accepted := checkPSDFactorQ G c
    asymmetries := gramAsymmetriesQ G
    negativeWeights := negativeFactorWeightsQ c
    entryMismatches := gramEntryMismatchesQ G (factorGramQ c.factors) }

/-- Audit acceptance has exactly the certificate-validity meaning. -/
theorem auditPSDFactorQ_accepted_iff
    {m : ℕ} (G : Gram m ℚ) (c : PSDFactorCertQ m) :
    (auditPSDFactorQ G c).accepted = true ↔ PSDFactorValidQ G c := by
  simpa [auditPSDFactorQ] using checkPSDFactorQ_eq_true_iff G c

/-- Acceptance of the structured audit report proves the target Gram matrix PSD. -/
theorem auditPSDFactorQ_sound
    {m : ℕ} (G : Gram m ℚ) (c : PSDFactorCertQ m)
    (h : (auditPSDFactorQ G c).accepted = true) :
    IsGramPosSemidef G := by
  apply checkPSDFactorQ_sound G c
  simpa [auditPSDFactorQ] using h

/-- Every reported asymmetry records the exact unequal target entries. -/
theorem mem_gramAsymmetriesQ_sound
    {m : ℕ} (G : Gram m ℚ) (a : GramAsymmetryQ m)
    (h : a ∈ gramAsymmetriesQ G) :
    a.left = G a.i a.j ∧
      a.right = G a.j a.i ∧
      a.left ≠ a.right := by
  unfold gramAsymmetriesQ at h
  simp only [List.mem_flatMap] at h
  rcases h with ⟨ij, hij, hitem⟩
  rcases ij with ⟨i, j⟩
  by_cases heq : G i j = G j i
  · simp [heq] at hitem
  · simp [heq] at hitem
    subst a
    exact ⟨rfl, rfl, heq⟩

/-- Every reported factorization mismatch names the exact expected and actual entries. -/
theorem mem_gramEntryMismatchesQ_sound
    {m : ℕ} (G actual : Gram m ℚ)
    (e : GramEntryMismatchQ m)
    (h : e ∈ gramEntryMismatchesQ G actual) :
    e.expected = G e.i e.j ∧
      e.actual = actual e.i e.j ∧
      e.expected ≠ e.actual := by
  unfold gramEntryMismatchesQ at h
  simp only [List.mem_flatMap] at h
  rcases h with ⟨ij, hij, hitem⟩
  rcases ij with ⟨i, j⟩
  by_cases heq : G i j = actual i j
  · simp [heq] at hitem
  · simp [heq] at hitem
    subst e
    exact ⟨rfl, rfl, heq⟩

/-- Every reported negative weight is strictly negative. -/
theorem mem_negativeFactorWeightsFromQ_sound
    {m : ℕ}
    (start : Nat) (factors : List (RankOneFactorQ m))
    (e : NegativeFactorWeightQ)
    (h : e ∈ negativeFactorWeightsFromQ start factors) :
    e.weight < 0 := by
  induction factors generalizing start with
  | nil =>
      simp [negativeFactorWeightsFromQ] at h
  | cons t ts ih =>
      by_cases hneg : t.weight < 0
      · simp [negativeFactorWeightsFromQ, hneg] at h
        rcases h with h | h
        · subst e
          exact hneg
        · exact ih (start := start + 1) h
      · have hrest :
          e ∈ negativeFactorWeightsFromQ (start + 1) ts := by
            simpa [negativeFactorWeightsFromQ, hneg] using h
        exact ih (start := start + 1) hrest

/-- Every item in the complete weight report is genuinely negative. -/
theorem mem_negativeFactorWeightsQ_sound
    {m : ℕ} (c : PSDFactorCertQ m)
    (e : NegativeFactorWeightQ)
    (h : e ∈ negativeFactorWeightsQ c) :
    e.weight < 0 := by
  exact mem_negativeFactorWeightsFromQ_sound 0 c.factors e h

end GramPEP
end LeanPEP
