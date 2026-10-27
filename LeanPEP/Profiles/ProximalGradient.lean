import LeanPEP.Profiles.Composite
import LeanPEP.GramPEP.Coordinate

/-!
# Positive-horizon proximal-gradient profile compiler

The parameter `n` encodes EXACTLY `n + 1` unit forward-backward steps.
The smooth sample order is `star, x_0, ..., x_(n+1)`; the nonsmooth
sample order is `star, x_1, ..., x_(n+1)`. There is deliberately no
subgradient sample at `x_0`: the algorithm does not supply one.

Value slots: `(f_star, f_0, ..., f_(n+1), h_star, h_1, ..., h_(n+1))`.
Gram basis: `(x_0-x_star, g_star, g_0, ..., g_(n+1), s_1, ..., s_(n+1))`.
Here residual index `j : Fin (n+1)` means `s_(j+1)`, not `s_j`.

All function inequalities are compiled by the EXISTING component-local
compiler. The ModelQ position/gradient fields remain dummy carrier fields;
only explicit constraints have actual sample semantics.
-/

namespace LeanPEP.Profiles.ProximalGradient

open LeanPEP.GramPEP

abbrev valueCount (n : ℕ) : ℕ := (n + 3) + (n + 2)
abbrev basisCount (n : ℕ) : ℕ := (n + 4) + (n + 1)

/-- Two disjoint blocks of value slots. -/
def smoothValueIndex {n : ℕ} (i : Fin (n + 3)) : Fin (valueCount n) :=
  Fin.castAdd (n + 2) i

def nonsmoothValueIndex {n : ℕ} (i : Fin (n + 2)) : Fin (valueCount n) :=
  Fin.natAdd (n + 3) i

def initialBasisIndex (n : ℕ) : Fin (basisCount n) :=
  Fin.castAdd (n + 1) (0 : Fin (n + 4))

def starBasisIndex (n : ℕ) : Fin (basisCount n) :=
  Fin.castAdd (n + 1) (1 : Fin (n + 4))

def gradientBasisIndex {n : ℕ} (i : Fin (n + 2)) : Fin (basisCount n) :=
  Fin.castAdd (n + 1) i.succ.succ

def residualBasisIndex {n : ℕ} (j : Fin (n + 1)) : Fin (basisCount n) :=
  Fin.natAdd (n + 4) j

theorem value_blocks_disjoint {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) :
    smoothValueIndex i ≠ nonsmoothValueIndex j := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [smoothValueIndex, nonsmoothValueIndex, Fin.val_castAdd, Fin.val_natAdd] at hv
  have hi := i.isLt
  omega

theorem smoothValueIndex_injective (n : ℕ) :
    Function.Injective (smoothValueIndex (n := n)) := by
  intro i j h
  have hv := congrArg (fun k : Fin (valueCount n) => k.val) h
  apply Fin.ext
  simpa only [smoothValueIndex, Fin.val_castAdd] using hv

theorem nonsmoothValueIndex_injective (n : ℕ) :
    Function.Injective (nonsmoothValueIndex (n := n)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [nonsmoothValueIndex, Fin.val_natAdd] at hv
  omega

/-- Every slot belongs to exactly one component block. -/
theorem valueIndex_covers {n : ℕ} (i : Fin (valueCount n)) :
    (∃ j, smoothValueIndex j = i) ∨ (∃ j, nonsmoothValueIndex j = i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact Or.inl ⟨j, rfl⟩
  · exact Or.inr ⟨j, rfl⟩

def initialVecQ (n : ℕ) : VecExpr (basisCount n) ℚ :=
  standardBasisExpr (𝕜 := ℚ) (initialBasisIndex n)

def starGradientQ (n : ℕ) : VecExpr (basisCount n) ℚ :=
  standardBasisExpr (𝕜 := ℚ) (starBasisIndex n)

def gradientVecQ {n : ℕ} (i : Fin (n + 2)) : VecExpr (basisCount n) ℚ :=
  standardBasisExpr (𝕜 := ℚ) (gradientBasisIndex i)

def residualVecQ {n : ℕ} (j : Fin (n + 1)) : VecExpr (basisCount n) ℚ :=
  standardBasisExpr (𝕜 := ℚ) (residualBasisIndex j)

/-- The symbolic implicit update. Indices beyond the declared horizon are
frozen, not wrapped modulo a Fin dimension. Public realization statements
below use only indices at most `n + 1`. -/
def positionVecQ (n : ℕ) : ℕ → VecExpr (basisCount n) ℚ
  | 0 => initialVecQ n
  | k + 1 => if hk : k < n + 1 then
      positionVecQ n k - gradientVecQ (⟨k, by omega⟩ : Fin (n + 2)) -
        residualVecQ (⟨k, hk⟩ : Fin (n + 1))
    else positionVecQ n k

@[simp] theorem positionVecQ_zero (n : ℕ) : positionVecQ n 0 = initialVecQ n := rfl

/-- Residual `j` belongs to the NEW point `x_(j+1)`. -/
theorem positionVecQ_succ {n : ℕ} (j : Fin (n + 1)) :
    positionVecQ n (j.val + 1) =
      positionVecQ n j.val - gradientVecQ j.castSucc - residualVecQ j := by
  have hindex : (⟨j.val, by omega⟩ : Fin (n + 2)) = j.castSucc := by
    apply Fin.ext
    rfl
  simp [positionVecQ, j.isLt, hindex]

private theorem positionVecQ_coordinate_zero {n : ℕ} (r : Fin (basisCount n))
    (hinit : initialVecQ n r = 0) (k : ℕ)
    (hg : ∀ j : Fin (n + 1), j.val < k → gradientVecQ j.castSucc r = 0)
    (hs : ∀ j : Fin (n + 1), j.val < k → residualVecQ j r = 0) :
    positionVecQ n k r = 0 := by
  revert hg hs
  induction k with
  | zero => intro _ _; exact hinit
  | succ k ih =>
      intro hg hs
      have hg' : ∀ j : Fin (n + 1), j.val < k → gradientVecQ j.castSucc r = 0 := by
        intro j hj
        exact hg j (by omega)
      have hs' : ∀ j : Fin (n + 1), j.val < k → residualVecQ j r = 0 := by
        intro j hj
        exact hs j (by omega)
      have hi := ih hg' hs'
      by_cases hk : k < n + 1
      · let j : Fin (n + 1) := ⟨k, hk⟩
        have hgj := hg j (by dsimp [j]; omega)
        have hsj := hs j (by dsimp [j]; omega)
        have heq := positionVecQ_succ j
        have hv := congrArg (fun v : VecExpr (basisCount n) ℚ => v r) heq
        change positionVecQ n (k + 1) r =
          positionVecQ n k r - gradientVecQ j.castSucc r - residualVecQ j r at hv
        rw [hv]
        simp only [hi, hgj, hsj, sub_self, sub_zero]
      · simpa only [positionVecQ, dif_neg hk] using hi

/-- No current or future smooth gradient can enter an earlier position. -/
theorem positionVecQ_gradient_causal {n : ℕ} (k : ℕ) (i : Fin (n + 2))
    (hki : k ≤ i.val) : positionVecQ n k (gradientBasisIndex i) = 0 := by
  apply positionVecQ_coordinate_zero
  · have hne : gradientBasisIndex i ≠ initialBasisIndex n := by
      intro h
      have hv := congrArg Fin.val h
      simp [gradientBasisIndex, initialBasisIndex] at hv
    simp [initialVecQ, standardBasisExpr, hne]
  · intro j hj
    have hne : gradientBasisIndex i ≠ gradientBasisIndex j.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp [gradientBasisIndex] at hv
      have hjv : j.val < k := hj
      omega
    simp [gradientVecQ, standardBasisExpr, hne]
  · intro j _
    have hne : gradientBasisIndex i ≠ residualBasisIndex j := by
      intro h
      have hv := congrArg Fin.val h
      simp [gradientBasisIndex, residualBasisIndex] at hv
      have hi := i.isLt
      omega
    simp [residualVecQ, standardBasisExpr, hne]

/-- Residual `s_(j+1)` is absent until its implicit proximal step completes. -/
theorem positionVecQ_residual_causal {n : ℕ} (k : ℕ) (i : Fin (n + 1))
    (hki : k ≤ i.val) : positionVecQ n k (residualBasisIndex i) = 0 := by
  apply positionVecQ_coordinate_zero
  · have hne : residualBasisIndex i ≠ initialBasisIndex n := by
      intro h
      have hv := congrArg Fin.val h
      simp [residualBasisIndex, initialBasisIndex] at hv
    simp [initialVecQ, standardBasisExpr, hne]
  · intro j _
    have hne : residualBasisIndex i ≠ gradientBasisIndex j.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp [residualBasisIndex, gradientBasisIndex] at hv
      have hj := j.isLt
      omega
    simp [gradientVecQ, standardBasisExpr, hne]
  · intro j hj
    have hne : residualBasisIndex i ≠ residualBasisIndex j := by
      intro h
      have hv := congrArg Fin.val h
      simp [residualBasisIndex] at hv
      omega
    simp [residualVecQ, standardBasisExpr, hne]

/-- The final smooth oracle sample is used for interpolation, never an update. -/
theorem terminal_gradient_unused (n : ℕ) (k : ℕ) (hk : k ≤ n + 1) :
    positionVecQ n k (gradientBasisIndex (Fin.last (n + 1))) = 0 :=
  positionVecQ_gradient_causal k _ hk

def smoothSamplesQ (n : ℕ) : Fin (n + 3) → Composite.SampleQ (valueCount n) (basisCount n) :=
  Fin.cases
    { valueIndex := smoothValueIndex 0, position := 0, oracle := starGradientQ n }
    (fun i => { valueIndex := smoothValueIndex i.succ
                position := positionVecQ n i.val
                oracle := gradientVecQ i })

def nonsmoothSamplesQ (n : ℕ) : Fin (n + 2) → Composite.SampleQ (valueCount n) (basisCount n) :=
  Fin.cases
    { valueIndex := nonsmoothValueIndex 0, position := 0, oracle := -starGradientQ n }
    (fun j => { valueIndex := nonsmoothValueIndex j.succ
                position := positionVecQ n (j.val + 1)
                oracle := residualVecQ j })

def smoothComponentQ (n : ℕ) : Composite.ComponentQ (valueCount n) (basisCount n) :=
  { functionClass := .oneSmoothConvex
    samples := (List.finRange (n + 3)).map (smoothSamplesQ n) }

def nonsmoothComponentQ (n : ℕ) : Composite.ComponentQ (valueCount n) (basisCount n) :=
  { functionClass := .convex
    samples := (List.finRange (n + 2)).map (nonsmoothSamplesQ n) }

def radiusExprQ (n : ℕ) : LinearExprQ (valueCount n) (basisCount n) :=
  LinearExprQ.sub (LinearExprQ.const _ _ 1) (LinearExprQ.gramNorm (initialVecQ n))

def objectiveQ (n : ℕ) : LinearExprQ (valueCount n) (basisCount n) :=
  LinearExprQ.sub
    (LinearExprQ.add
      (LinearExprQ.valueVar (smoothValueIndex (Fin.last (n + 2))))
      (LinearExprQ.valueVar (nonsmoothValueIndex (Fin.last (n + 1)))))
    (LinearExprQ.add (LinearExprQ.valueVar (smoothValueIndex 0))
      (LinearExprQ.valueVar (nonsmoothValueIndex 0)))

def profileQ (n : ℕ) : Composite.ProfileQ (valueCount n) (basisCount n) :=
  { components := [smoothComponentQ n, nonsmoothComponentQ n]
    assumptions := [radiusExprQ n]
    objective := objectiveQ n }

def modelQ (n : ℕ) : ModelQ (valueCount n) (basisCount n) :=
  Composite.compileModelQ (profileQ n)

/-- Deterministic constraint order, inherited from the component compiler. -/
theorem modelQ_constraints (n : ℕ) : (modelQ n).assumptions =
    ((List.finRange (n + 3)).flatMap fun i => (List.finRange (n + 3)).map fun j =>
      Composite.interpolationExprQ .oneSmoothConvex (smoothSamplesQ n i) (smoothSamplesQ n j)) ++
    ((List.finRange (n + 2)).flatMap fun i => (List.finRange (n + 2)).map fun j =>
      Composite.interpolationExprQ .convex (nonsmoothSamplesQ n i) (nonsmoothSamplesQ n j)) ++
    [radiusExprQ n] := by
  simp [modelQ, Composite.compileModelQ, Composite.compileConstraintsQ, profileQ,
    smoothComponentQ, nonsmoothComponentQ, Composite.componentConstraintsQ,
    List.flatMap_map, List.map_map, Function.comp_def, List.append_assoc]

private theorem pair_list_length {α β γ : Type*} (xs : List α) (ys : List β)
    (f : α → β → γ) :
    (xs.flatMap (fun a => ys.map (f a))).length = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem modelQ_constraint_count (n : ℕ) :
    (modelQ n).assumptions.length = (n + 3) ^ 2 + (n + 2) ^ 2 + 1 := by
  rw [modelQ_constraints]
  simp only [List.length_append, pair_list_length, List.length_finRange,
    List.length_singleton, pow_two, Nat.add_assoc]

/-- Only explicit constraints, PSD, a matching objective, and empty implicit
interpolation terms are used to interpret a checked certificate. -/
theorem certificate_upper {n : ℕ} (c : UpperCertQ (modelQ n))
    (hcheck : checkUpperCertQ c = true) (hempty : c.interpTerms = [])
    (hobjective : c.objective = objectiveQ n)
    (d : DataR (Fin (valueCount n)) (basisCount n))
    (hpsd : IsGramPosSemidef d.gram) (hc : AssumptionsFeasibleR (modelQ n) d) :
    (objectiveQ n).evalR d ≤ (c.bound : ℝ) :=
  Composite.certificate_upper (profileQ n) c hcheck hempty hobjective d hpsd hc

end LeanPEP.Profiles.ProximalGradient
