import LeanPEP.Toy.FiniteGD.RationalChecker

/-!
# Bridge from exact rational trajectories to real finite PEP semantics

A successful executable rational check can be transported to the real finite
PEP layer because positions, gradients, values, and every interpolation slack
are preserved by the canonical cast `ℚ → ℝ`.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD

/-- Cast exact rational trajectory data into real trajectory data. -/
noncomputable def toRealData {N : ℕ} (d : DataQ N) : DataR N :=
  { grad := fun k => (d.grad k : ℝ)
    value := fun k => (d.value k : ℝ) }

/-- Casting commutes with the recursively generated prefix sum. -/
theorem prefixSum_cast
    {N : ℕ} (g : Fin (N + 1) → ℚ) :
    ∀ (k : ℕ) (hk : k ≤ N + 1),
      ((prefixSum g k hk : ℚ) : ℝ) =
        prefixSum (fun i => (g i : ℝ)) k hk := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [prefixSum]
  | succ k ih =>
      intro hk
      simp [prefixSum, ih]

/-- Casting preserves every generated position. -/
@[simp] theorem x_toRealData
    {N : ℕ} (d : DataQ N) (i : Point N) :
    x (𝕜 := ℝ) (toRealData d) i =
      (((x (𝕜 := ℚ) d i : ℚ) : ℝ)) := by
  cases i with
  | star =>
      simp [x]
  | iter k =>
      simp [x, iterX, toRealData, prefixSum_cast]

/-- Casting preserves every gradient sample. -/
@[simp] theorem gradAt_toRealData
    {N : ℕ} (d : DataQ N) (i : Point N) :
    gradAt (𝕜 := ℝ) (toRealData d) i =
      (((gradAt (𝕜 := ℚ) d i : ℚ) : ℝ)) := by
  cases i <;> simp [gradAt, toRealData]

/-- Casting preserves every function-value sample. -/
@[simp] theorem valueAt_toRealData
    {N : ℕ} (d : DataQ N) (i : Point N) :
    valueAt (𝕜 := ℝ) (toRealData d) i =
      (((valueAt (𝕜 := ℚ) d i : ℚ) : ℝ)) := by
  cases i <;> simp [valueAt, toRealData]

/-- Casting preserves every exact interpolation slack. -/
@[simp] theorem slack_toRealData
    {N : ℕ} (d : DataQ N) (i j : Point N) :
    slack (𝕜 := ℝ) (toRealData d) i j =
      (((slack (𝕜 := ℚ) d i j : ℚ) : ℝ)) := by
  simp [slack]

/-- Rational feasibility implies feasibility of the cast real trajectory. -/
theorem feasibleQ_toReal
    {N : ℕ} (d : DataQ N)
    (h : Feasible d) :
    Feasible (toRealData d) := by
  intro i j
  rw [slack_toRealData]
  exact Rat.cast_nonneg.mpr (h i j)

/-- A successful generated checker produces real finite PEP feasibility. -/
theorem checkFeasibleQ_sound_real
    {N : ℕ} (d : DataQ N)
    (h : checkFeasibleQ d = true) :
    Feasible (toRealData d) :=
  feasibleQ_toReal d (checkFeasibleQ_sound d h)

end FiniteGD
end Toy
end LeanPEP
