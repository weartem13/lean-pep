import LeanPEP.ActualFunction.ForwardBackwardStability
import LeanPEP.ActualFunction.ProximalGradientHilbert

/-!
# Stability, finite energy and asymptotic regularity of the existing iteration

No recursion is added. The exact C6 iteration is nonexpansive in its initial
point; with a composite minimizer it has a Fejer energy estimate. The squared
last-step bound and vanishing step norms are consequences, not sharp PEP
claims. Vanishing step norms are not convergence of the iterates to a point.
Approximate trajectories receive a distance-to-exact bound, not an inexact
function-value rate. The Hilbert wrappers use C7 to discharge HasProx.
-/

noncomputable section
open Filter
open scoped NNReal Topology BigOperators
namespace LeanPEP.ActualFunction.ProximalGradientCanonical
open ProximalScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Same function pair, same scale, two arbitrary initial points. -/
theorem iterate_norm_sub_le {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (x0 y0 : E) (N : ℕ) :
    ‖iterate hp g x0 N-iterate hp g y0 N‖ ≤ ‖x0-y0‖ := by
  induction N with
  | zero => exact le_refl _
  | succ N ih =>
    rw [iterate_succ_eq_step hp g x0 N, iterate_succ_eq_step hp g y0 N]
    exact (forwardBackwardStep_norm_sub_le hp hf hL hh _ _).trans ih

/-- A single Fejer step, with the residual-square margin retained. -/
theorem iterate_fejer_energy {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) (k : ℕ) :
    ‖iterate hp g x0 (k+1)-xStar‖^2 +
      (1/2 : ℝ)*‖iterate hp g x0 (k+1)-iterate hp g x0 k‖^2 ≤
        ‖iterate hp g x0 k-xStar‖^2 := by
  have he := forwardBackwardStep_energy hp hf hL hh (iterate hp g x0 k) xStar
  rw [forwardBackwardStep_fixed_of_minimizer hp hf hL hh hmin,
    ← iterate_succ_eq_step hp g x0 k] at he
  have heq : (iterate hp g x0 k-xStar)-(iterate hp g x0 (k+1)-xStar) =
      -(iterate hp g x0 (k+1)-iterate hp g x0 k) := by abel
  rw [heq, norm_neg] at he
  exact he

/-- Distances to each supplied global minimizer do not increase. -/
theorem iterate_distance_antitone {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    Antitone (fun k => ‖iterate hp g x0 k-xStar‖) := by
  apply antitone_nat_of_succ_le
  intro k
  have he := iterate_fejer_energy hp hf hL hh hmin x0 k
  have hn := sq_nonneg ‖iterate hp g x0 (k+1)-iterate hp g x0 k‖
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith only [he, hn]

/-- A finite sum with a remaining terminal-distance term; N=0 is included. -/
theorem iterate_sum_step_energy {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) (N : ℕ) :
    ‖iterate hp g x0 N-xStar‖^2 +
      (1/2 : ℝ)*(∑ k ∈ Finset.range N, ‖iterate hp g x0 (k+1)-iterate hp g x0 k‖^2) ≤
        ‖x0-xStar‖^2 := by
  induction N with
  | zero => simp only [iterate_zero, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero, le_refl]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have he := iterate_fejer_energy hp hf hL hh hmin x0 N
    linarith only [ih, he]

/-- Step norms do not increase. No minimizer is needed for this fact. -/
theorem iterate_step_norm_antitone {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (x0 : E) :
    Antitone (fun k => ‖iterate hp g x0 (k+1)-iterate hp g x0 k‖) := by
  apply antitone_nat_of_succ_le
  intro k
  change ‖iterate hp g x0 ((k+1)+1)-iterate hp g x0 (k+1)‖ ≤ _
  rw [iterate_succ_eq_step hp g x0 (k+1), iterate_succ_eq_step hp g x0 k]
  exact forwardBackwardStep_norm_sub_le hp hf hL hh _ _

/-- A derived last-step estimate; the constant two is not asserted optimal. -/
theorem iterate_last_step_norm_sq_le {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) (N : ℕ) :
    ‖iterate hp g x0 (N+1)-iterate hp g x0 N‖^2 ≤ 2*‖x0-xStar‖^2/((N : ℝ)+1) := by
  have ha := iterate_step_norm_antitone hp hf hL hh x0
  have hsum : ((N : ℝ)+1)*‖iterate hp g x0 (N+1)-iterate hp g x0 N‖^2 ≤
      ∑ k ∈ Finset.range (N+1), ‖iterate hp g x0 (k+1)-iterate hp g x0 k‖^2 := by
    calc
      ((N : ℝ)+1)*‖iterate hp g x0 (N+1)-iterate hp g x0 N‖^2 =
          ∑ _k ∈ Finset.range (N+1), ‖iterate hp g x0 (N+1)-iterate hp g x0 N‖^2 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
          Nat.cast_one]
      _ ≤ _ := Finset.sum_le_sum (fun k hk =>
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
          (ha (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))
  have he := iterate_sum_step_energy hp hf hL hh hmin x0 (N+1)
  have hn := sq_nonneg ‖iterate hp g x0 (N+1)-xStar‖
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ)+1)).mpr
  have hb : ((N : ℝ)+1)*‖iterate hp g x0 (N+1)-iterate hp g x0 N‖^2 ≤
      2*‖x0-xStar‖^2 := by linarith only [hsum, he, hn]
  simpa only [mul_comm] using hb

/-- Asymptotic regularity, not convergence of the point sequence. -/
theorem iterate_step_norm_tendsto_zero {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    Tendsto (fun k => ‖iterate hp g x0 (k+1)-iterate hp g x0 k‖) atTop (𝓝 0) := by
  have hupper : Tendsto (fun k : ℕ => 2*‖x0-xStar‖^2/((k : ℝ)+1)) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => 2*‖x0-xStar‖^2) atTop
        (𝓝 (2*‖x0-xStar‖^2)) := tendsto_const_nhds
    simpa only [mul_zero, mul_one_div] using
      hc.mul tendsto_one_div_add_atTop_nhds_zero_nat
  have hsq : Tendsto (fun k => ‖iterate hp g x0 (k+1)-iterate hp g x0 k‖^2) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => sq_nonneg _) (iterate_last_step_norm_sq_le hp hf hL hh hmin x0)
  have hroot : Tendsto (fun t : ℝ => Real.sqrt t) (𝓝 0) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  have hcomp := hroot.comp hsq
  have hfun :
      ((fun t : ℝ => Real.sqrt t) ∘
        (fun k : ℕ => ‖iterate hp g x0 (k+1)-iterate hp g x0 k‖^2)) =
      (fun k : ℕ => ‖iterate hp g x0 (k+1)-iterate hp g x0 k‖) := by
    funext k
    exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun] at hcomp
  exact hcomp

/-- A posteriori distance to the exact trajectory for approximate steps.
Errors are pointwise distances to the same exact map; no inexact objective
rate, summable-errors convergence theorem, or solver correctness is assumed. -/
theorem inexact_iterate_distance_le {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (x0 : E) (z : ℕ → E) (eps : ℕ → ℝ) (N : ℕ)
    (herr : ∀ k < N, ‖z (k+1)-forwardBackwardStep hp g (z k)‖ ≤ eps k) :
    ‖z N-iterate hp g x0 N‖ ≤ ‖z 0-x0‖ + ∑ k ∈ Finset.range N, eps k := by
  revert herr
  induction N with
  | zero =>
    intro _
    simp only [iterate_zero, Finset.range_zero, Finset.sum_empty, add_zero, le_refl]
  | succ N ih =>
    intro herr
    have hpref := ih (fun k hk => herr k (by omega))
    have hlocal := herr N (by omega)
    have hstable := forwardBackwardStep_norm_sub_le hp hf hL hh (z N) (iterate hp g x0 N)
    have htri := dist_triangle (z (N+1)) (forwardBackwardStep hp g (z N))
      (forwardBackwardStep hp g (iterate hp g x0 N))
    simp only [dist_eq_norm] at htri
    rw [iterate_succ_eq_step hp g x0 N, Finset.sum_range_succ]
    linarith only [hpref, hlocal, hstable, htri]

/-- Gradient errors followed by exact prox solves satisfy the same error budget. -/
theorem inexact_gradient_distance_le {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (x0 : E) (z e : ℕ → E) (N : ℕ)
    (hstep : ∀ k < N, z (k+1) = proxMap hp (z k-(L : ℝ)⁻¹ • (g (z k)+e k))) :
    ‖z N-iterate hp g x0 N‖ ≤ ‖z 0-x0‖ +
      ∑ k ∈ Finset.range N, (L : ℝ)⁻¹*‖e k‖ := by
  apply inexact_iterate_distance_le hp hf hL hh x0 z (fun k => (L : ℝ)⁻¹*‖e k‖) N
  intro k hk
  rw [hstep k hk]
  exact forwardBackwardStep_oracle_error hp hL hh g (z k) (e k)

/-- C7 automatically supplies solvability. No minimizer is needed for input
stability, and no extra finite-dimensionality assumption appears. -/
theorem hilbertIterate_norm_sub_le [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) (x0 y0 : E) (N : ℕ) :
    ‖hilbertIterate L h hL hh hcont g x0 N-hilbertIterate L h hL hh hcont g y0 N‖ ≤
      ‖x0-y0‖ :=
  iterate_norm_sub_le (hasProx_of_continuous hL hh hcont) hf.toFirstOrder hL hh x0 y0 N

theorem hilbertIterate_sum_step_energy [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) (N : ℕ) :
    ‖hilbertIterate L h hL hh hcont g x0 N-xStar‖^2 +
      (1/2 : ℝ)*(∑ k ∈ Finset.range N,
        ‖hilbertIterate L h hL hh hcont g x0 (k+1)-hilbertIterate L h hL hh hcont g x0 k‖^2) ≤
      ‖x0-xStar‖^2 :=
  iterate_sum_step_energy (hasProx_of_continuous hL hh hcont) hf.toFirstOrder hL hh hmin x0 N

theorem hilbertIterate_last_step_norm_sq_le [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) (N : ℕ) :
    ‖hilbertIterate L h hL hh hcont g x0 (N+1)-hilbertIterate L h hL hh hcont g x0 N‖^2 ≤
      2*‖x0-xStar‖^2/((N : ℝ)+1) :=
  iterate_last_step_norm_sq_le (hasProx_of_continuous hL hh hcont) hf.toFirstOrder hL hh hmin x0 N

theorem hilbertIterate_step_norm_tendsto_zero [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    Tendsto (fun k =>
      ‖hilbertIterate L h hL hh hcont g x0 (k+1)-hilbertIterate L h hL hh hcont g x0 k‖)
      atTop (𝓝 0) :=
  iterate_step_norm_tendsto_zero (hasProx_of_continuous hL hh hcont)
    hf.toFirstOrder hL hh hmin x0

/-- Same a posteriori error bound with the C7 existence proof supplied. -/
theorem hilbertIterate_inexact_distance_le [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (x0 : E) (z : ℕ → E) (eps : ℕ → ℝ) (N : ℕ)
    (herr : ∀ k < N,
      ‖z (k+1)-forwardBackwardStep (hasProx_of_continuous hL hh hcont) g (z k)‖ ≤ eps k) :
    ‖z N-hilbertIterate L h hL hh hcont g x0 N‖ ≤
      ‖z 0-x0‖ + ∑ k ∈ Finset.range N, eps k :=
  inexact_iterate_distance_le (hasProx_of_continuous hL hh hcont)
    hf.toFirstOrder hL hh x0 z eps N herr

end LeanPEP.ActualFunction.ProximalGradientCanonical
