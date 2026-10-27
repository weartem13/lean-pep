import LeanPEP.ActualFunction.HuberWitness
import LeanPEP.ActualFunction.ParametricGDActual
import LeanPEP.Toy.FiniteGD.ParametricUpperTelescoping
import Mathlib.Tactic

/-!
# Exact Huber-witness gradient-descent trajectory and attainment

The first Huber-witness slice established an exact normalized first-order
smooth-convex contract for the one-dimensional function/gradient pair with
threshold

```text
q_N = 1 / (2N + 1).
```

This file proves the elementary trajectory algebra that turns that pair into a
matching lower witness for the arbitrary-length normalized GD upper theorem.
For

```text
z_k = 1 - k q_N,
```

all points needed through the `N`-th update remain on the affine branch of the
Huber function, so the clipped gradient is exactly `q_N`.  Consequently the
actual unit-step recursion starting from `1` follows `z_k`, and its final
function-value gap is exactly

```text
1 / (4N + 2) = gdBoundQ N.
```

This slice proves exact attainment for the already verified first-order
contract.  It deliberately does not yet prove differentiability or the
analytic Lipschitz-gradient interface; those regularity obligations remain a
separate follow-up slice.
-/

noncomputable section

namespace LeanPEP
namespace ActualFunction
namespace HuberWitness

open Toy.FiniteGD.ParametricUpper
open ParametricGDActual

/-- The threshold is normalized by its positive denominator. -/
theorem threshold_den_mul (N : ℕ) :
    (((2 * N + 1 : ℕ) : ℝ)) * threshold N = 1 := by
  unfold threshold
  have hden : (((2 * N + 1 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  field_simp [hden]

/-- Every candidate iterate through index `N` lies on the affine Huber branch. -/
theorem threshold_le_witnessPoint
    (N k : ℕ) (hk : k ≤ N) :
    threshold N ≤ witnessPoint N k := by
  have hcount : k + 1 ≤ 2 * N + 1 := by
    omega
  have hcountR :
      (((k + 1 : ℕ) : ℝ)) ≤ (((2 * N + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hcount
  have hthreshold : 0 ≤ threshold N :=
    le_of_lt (threshold_pos N)
  have hscaled :=
    mul_le_mul_of_nonneg_right hcountR hthreshold
  have hnormalize := threshold_den_mul N
  unfold witnessPoint
  push_cast at hscaled hnormalize
  nlinarith

/-- The clipped gradient is constant along every required candidate iterate. -/
@[simp] theorem witnessGradient_witnessPoint
    (N k : ℕ) (hk : k ≤ N) :
    witnessGradient N (witnessPoint N k) = threshold N := by
  simpa [witnessGradient] using
    huberGradient_of_ge (threshold_le_witnessPoint N k hk)

/-- The function is on its affine branch along every required candidate
iterate. -/
theorem witnessFunction_witnessPoint
    (N k : ℕ) (hk : k ≤ N) :
    witnessFunction N (witnessPoint N k) =
      threshold N * witnessPoint N k - threshold N ^ 2 / 2 := by
  simpa [witnessFunction] using
    huberFunction_of_ge (threshold_le_witnessPoint N k hk)

/-- The explicit candidate points satisfy one unit-step GD update. -/
theorem witnessPoint_unitGD_step
    (N k : ℕ) (hk : k ≤ N) :
    witnessPoint N (k + 1) =
      witnessPoint N k - witnessGradient N (witnessPoint N k) := by
  rw [witnessPoint_succ, witnessGradient_witnessPoint N k hk]

/-- The actual unit-step recursion starting at `1` follows the closed-form
points through index `N + 1`. -/
theorem unitGDIterate_eq_witnessPoint
    (N : ℕ) :
    ∀ k : ℕ, k ≤ N + 1 →
      unitGDIterate (witnessGradient N) 1 k = witnessPoint N k := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp
  | succ k ih =>
      intro hk
      have hkN : k ≤ N := by
        omega
      have hkSucc : k ≤ N + 1 := by
        omega
      calc
        unitGDIterate (witnessGradient N) 1 (k + 1) =
            unitGDIterate (witnessGradient N) 1 k -
              witnessGradient N
                (unitGDIterate (witnessGradient N) 1 k) := rfl
        _ = witnessPoint N k -
              witnessGradient N (witnessPoint N k) := by
            simp only [ih hkSucc]
        _ = witnessPoint N (k + 1) :=
          (witnessPoint_unitGD_step N k hkN).symm

/-- In particular, the `N`-th actual iterate is the advertised witness point. -/
theorem unitGDIterate_final (N : ℕ) :
    unitGDIterate (witnessGradient N) 1 N = witnessPoint N N :=
  unitGDIterate_eq_witnessPoint N N (by omega)

/-- The final point is the midpoint between `1` and the threshold. -/
theorem witnessPoint_final_eq_midpoint (N : ℕ) :
    witnessPoint N N = (1 + threshold N) / 2 := by
  have hnormalize := threshold_den_mul N
  unfold witnessPoint
  push_cast at hnormalize
  nlinarith

/-- The final Huber value is one half of the threshold. -/
theorem witnessFunction_final_eq_half_threshold (N : ℕ) :
    witnessFunction N (witnessPoint N N) =
      ((1 : ℝ) / 2) * threshold N := by
  rw [witnessFunction_witnessPoint N N le_rfl,
    witnessPoint_final_eq_midpoint]
  ring

/-- One half of the real threshold is the cast of the exact certified bound. -/
theorem half_threshold_eq_gdBoundQ_cast (N : ℕ) :
    ((1 : ℝ) / 2) * threshold N = (gdBoundQ N : ℝ) := by
  rw [threshold_eq_gdCenterQ_cast, gdBoundQ_eq_half_centerQ]
  norm_num

/-- The real cast of `gdBoundQ` has its advertised closed form. -/
theorem gdBoundQ_cast_eq_closed (N : ℕ) :
    (gdBoundQ N : ℝ) =
      (1 : ℝ) / (((4 * N + 2 : ℕ) : ℝ)) := by
  norm_num [gdBoundQ]

/-- The explicit final point attains the exact certified bound. -/
theorem witnessFunction_final_eq_bound (N : ℕ) :
    witnessFunction N (witnessPoint N N) = (gdBoundQ N : ℝ) := by
  rw [witnessFunction_final_eq_half_threshold,
    half_threshold_eq_gdBoundQ_cast]

/-- The actual unit-step GD execution attains the exact normalized upper bound. -/
theorem witness_unitGD_attains_bound (N : ℕ) :
    witnessFunction N
        (unitGDIterate (witnessGradient N) 1 N) -
      witnessFunction N 0 =
        (gdBoundQ N : ℝ) := by
  rw [unitGDIterate_final, witnessFunction_final_eq_bound,
    witnessFunction_zero]
  ring

/-- User-facing closed form of the exact attained value. -/
theorem witness_unitGD_attains_closed_form (N : ℕ) :
    witnessFunction N
        (unitGDIterate (witnessGradient N) 1 N) -
      witnessFunction N 0 =
        (1 : ℝ) / (((4 * N + 2 : ℕ) : ℝ)) := by
  rw [witness_unitGD_attains_bound, gdBoundQ_cast_eq_closed]

/-- A compact proof-carrying normalized lower witness: first-order class
membership, stationarity and global minimality at zero, unit initial radius,
and exact attainment of the certified bound. -/
theorem normalized_lower_witness (N : ℕ) :
    IsOneSmoothConvexFirstOrder
        (witnessFunction N) (witnessGradient N) ∧
      witnessGradient N 0 = 0 ∧
      (∀ x : ℝ, witnessFunction N 0 ≤ witnessFunction N x) ∧
      ‖(1 : ℝ) - 0‖ ^ 2 ≤ 1 ∧
      witnessFunction N
          (unitGDIterate (witnessGradient N) 1 N) -
        witnessFunction N 0 =
          (gdBoundQ N : ℝ) := by
  constructor
  · exact witness_firstOrder N
  constructor
  · exact witnessGradient_zero N
  constructor
  · exact witness_zero_isGlobalMin N
  constructor
  · norm_num
  · exact witness_unitGD_attains_bound N

end HuberWitness
end ActualFunction
end LeanPEP
