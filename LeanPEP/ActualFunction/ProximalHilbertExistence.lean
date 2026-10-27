import LeanPEP.ActualFunction.CompositeOptimality
import LeanPEP.ActualFunction.StrongMidpointMinimizer

/-!
# Proximal existence on a real Hilbert space

Continuity is an explicit hypothesis in this infinite-dimensional interface.
A local upper bound and convexity yield a radial affine lower bound. The
positive quadratic penalty is bounded below and has the L/8 midpoint gap.
A minimizing sequence therefore converges by completeness, without compact
balls. The conclusion is the original `ProximalScaling.IsProxPoint` predicate.

This file does not claim that an arbitrary, potentially discontinuous,
real-valued convex function on a Hilbert space admits a proximal point.
-/

noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalScaling

open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Local boundedness above on a ball gives a global radial lower bound.
The proof works without finite dimension or completeness. -/
theorem norm_lower_bound_of_local_upper {h : E → ℝ} (hh : ConvexOn ℝ Set.univ h)
    (v : E) {r M : ℝ} (hr : 0 < r)
    (hupper : ∀ y, ‖y-v‖ ≤ r → h y ≤ h v + M) (x : E) :
    h v - (M/r)*‖x-v‖ ≤ h x := by
  by_cases hx : x = v
  · simp only [hx, sub_self, norm_zero, mul_zero, sub_zero, le_refl]
  let d : ℝ := ‖x-v‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hden : 0 < d+r := add_pos hd hr
  let y : E := v - (r/d) • (x-v)
  have hyv : y-v = -((r/d) • (x-v)) := by dsimp [y]; abel
  have hynorm : ‖y-v‖ = r := by
    rw [hyv, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hd)]
    change (r/d)*d = r
    exact div_mul_cancel₀ r (ne_of_gt hd)
  have hweight : r/(d+r) + d/(d+r) = 1 := by
    field_simp [ne_of_gt hden] <;> ring
  have hcancel : (d/(d+r))*(r/d) = r/(d+r) := by
    field_simp [ne_of_gt hd, ne_of_gt hden] <;> ring
  have hcomb : (r/(d+r)) • x + (d/(d+r)) • y = v := by
    dsimp only [y]
    rw [smul_sub, smul_smul, hcancel, smul_sub]
    calc
      _ = (r/(d+r) + d/(d+r)) • v := by rw [add_smul]; abel
      _ = v := by rw [hweight, one_smul]
  have hconv := hh.2 (mem_univ x) (mem_univ y)
    (le_of_lt (div_pos hr hden)) (le_of_lt (div_pos hd hden)) hweight
  rw [hcomb] at hconv
  simp only [smul_eq_mul] at hconv
  have hbound : h v ≤ (r/(d+r))*h x + (d/(d+r))*(h v+M) :=
    hconv.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
      (hupper y (le_of_eq hynorm)) (le_of_lt (div_pos hd hden))))
  have hclear := mul_le_mul_of_nonneg_left hbound (le_of_lt hden)
  have hright : (d+r)*((r/(d+r))*h x + (d/(d+r))*(h v+M)) =
      r*h x + d*(h v+M) := by
    field_simp [ne_of_gt hden] <;> ring
  rw [hright] at hclear
  have hscaled : r*(h v-(M/r)*d) ≤ r*h x := by
    have hMr : (M/r)*r = M := div_mul_cancel₀ M (ne_of_gt hr)
    calc
      r*(h v-(M/r)*d) = r*h v-d*M := by
        calc
          _ = r*h v-d*((M/r)*r) := by ring
          _ = r*h v-d*M := by rw [hMr]
      _ = (d+r)*h v-d*(h v+M) := by ring
      _ ≤ r*h x := (sub_le_iff_le_add).mpr hclear
  exact le_of_mul_le_mul_left hscaled hr

/-- Continuity at the chosen center supplies the local upper bound; no compact
ball or globally bounded-above hypothesis is needed. -/
theorem exists_norm_lower_bound_of_continuousAt {h : E → ℝ}
    (hh : ConvexOn ℝ Set.univ h) (v : E) (hcont : ContinuousAt h v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, h v - C*‖x-v‖ ≤ h x := by
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hcont (1 : ℝ) zero_lt_one
  have hr : 0 < δ/2 := half_pos hδ
  have hupper : ∀ y, ‖y-v‖ ≤ δ/2 → h y ≤ h v+1 := by
    intro y hy
    have hdist : dist y v < δ := by
      rw [dist_eq_norm]
      exact hy.trans_lt (half_lt_self hδ)
    have hhnear := hnear hdist
    rw [Real.dist_eq] at hhnear
    have hdiff : h y-h v < 1 := (abs_lt.mp hhnear).2
    linarith only [hdiff]
  refine ⟨1/(δ/2), by positivity, ?_⟩
  exact norm_lower_bound_of_local_upper hh v hr hupper

/-- Auxiliary objective, exactly the norm form of the existing prox predicate. -/
def hilbertProxObjective (L : ℝ≥0) (h : E → ℝ) (v x : E) : ℝ :=
  h x + ((L : ℝ)/2)*‖x-v‖^2

theorem hilbertProxObjective_continuous (L : ℝ≥0) {h : E → ℝ}
    (hcont : Continuous h) (v : E) : Continuous (hilbertProxObjective L h v) := by
  change Continuous (fun x : E => h x + ((L : ℝ)/2)*‖x-v‖^2)
  exact hcont.add (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2))

/-- Completing the square proves an actual lower bound for the whole range,
including when h itself is unbounded below. -/
theorem hilbertProxObjective_bddBelow {L : ℝ≥0} {h : E → ℝ}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (hcont : Continuous h) (v : E) : BddBelow (Set.range (hilbertProxObjective L h v)) := by
  obtain ⟨C, hC, hlower⟩ := exists_norm_lower_bound_of_continuousAt hh v hcont.continuousAt
  refine ⟨h v-C^2/(2*(L : ℝ)), ?_⟩
  rintro _ ⟨x, rfl⟩
  have hs : 0 ≤ ((L : ℝ)/2)*(‖x-v‖-C/(L : ℝ))^2 := by positivity
  have hid : h v-C^2/(2*(L : ℝ)) + ((L : ℝ)/2)*(‖x-v‖-C/(L : ℝ))^2 =
      h v-C*‖x-v‖ + ((L : ℝ)/2)*‖x-v‖^2 := by
    field_simp [ne_of_gt hL] <;> ring
  calc
    h v-C^2/(2*(L : ℝ)) ≤
        h v-C^2/(2*(L : ℝ)) + ((L : ℝ)/2)*(‖x-v‖-C/(L : ℝ))^2 :=
      le_add_of_nonneg_right hs
    _ = h v-C*‖x-v‖ + ((L : ℝ)/2)*‖x-v‖^2 := hid
    _ ≤ hilbertProxObjective L h v x := add_le_add (hlower x) (le_refl _)

/-- The L/8 midpoint gap is an exact consequence of the inner-product norm
identity and convexity of h. It is not inferred from bounded sublevel sets. -/
theorem hilbertProxObjective_midpoint_gap (L : ℝ≥0) {h : E → ℝ}
    (hh : ConvexOn ℝ Set.univ h) (v x y : E) :
    hilbertProxObjective L h v ((1/2 : ℝ) • x + (1/2 : ℝ) • y) ≤
      (hilbertProxObjective L h v x + hilbertProxObjective L h v y)/2 -
        ((L : ℝ)/8)*‖x-y‖^2 := by
  have hconv := hh.2 (mem_univ x) (mem_univ y)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ)+(1/2 : ℝ)=1)
  simp only [smul_eq_mul] at hconv
  have hvec : (1/2 : ℝ) • x + (1/2 : ℝ) • y - v =
      (1/2 : ℝ) • ((x-v)+(y-v)) := by module
  have hdiff : (x-v)-(y-v) = x-y := by abel
  have hnorm : ‖(1/2 : ℝ) • x + (1/2 : ℝ) • y-v‖^2 =
      (‖x-v‖^2+‖y-v‖^2)/2 - ‖x-y‖^2/4 := by
    rw [hvec, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2), mul_pow]
    rw [norm_add_sq_real (x-v) (y-v), ← hdiff, norm_sub_sq_real (x-v) (y-v)]
    ring
  calc
    hilbertProxObjective L h v ((1/2 : ℝ) • x + (1/2 : ℝ) • y) =
        h ((1/2 : ℝ) • x + (1/2 : ℝ) • y) +
          ((L : ℝ)/2)*((‖x-v‖^2+‖y-v‖^2)/2 - ‖x-y‖^2/4) := by
      rw [hilbertProxObjective, hnorm]
    _ ≤ ((1/2 : ℝ)*h x+(1/2 : ℝ)*h y) +
          ((L : ℝ)/2)*((‖x-v‖^2+‖y-v‖^2)/2 - ‖x-y‖^2/4) :=
      add_le_add hconv (le_refl _)
    _ = (hilbertProxObjective L h v x + hilbertProxObjective L h v y)/2 -
        ((L : ℝ)/8)*‖x-y‖^2 := by dsimp only [hilbertProxObjective]; ring

/-- Every positive-parameter prox problem for a continuous real-valued convex
function on a real Hilbert space has a solution. No finite dimension is used. -/
theorem exists_isProxPoint_hilbert [CompleteSpace E] {L : ℝ≥0} {h : E → ℝ}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (hcont : Continuous h) (v : E) : ∃ x, IsProxPoint L h v x := by
  obtain ⟨z, hz⟩ := StrongMidpointMinimizer.exists_minimizer_of_midpoint_gap
    (by positivity : (0 : ℝ) < (L : ℝ)/8)
    (hilbertProxObjective_continuous L hcont v)
    (hilbertProxObjective_bddBelow hL hh hcont v)
    (hilbertProxObjective_midpoint_gap L hh v)
  exact ⟨z, (isProxPoint_iff_norm L h v z).mpr hz⟩

/-- Uniqueness is the existing C5 optimality result; only existence is new. -/
theorem existsUnique_isProxPoint_hilbert [CompleteSpace E] {L : ℝ≥0} {h : E → ℝ}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (hcont : Continuous h) (v : E) : ∃! x, IsProxPoint L h v x := by
  obtain ⟨x, hx⟩ := exists_isProxPoint_hilbert hL hh hcont v
  exact ⟨x, hx, fun y hy => isProxPoint_unique hL hh hx hy⟩

end LeanPEP.ActualFunction.ProximalScaling
