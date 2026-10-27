import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Summable additive errors and asymptotic regularity

No algorithm, prox selector, weak topology or certificate is defined here.
The tail-corrected distance is antitone; the uncorrected distance need not be.
A positive fixed-point energy margin, not nonexpansiveness alone, makes the
residual of an inexact orbit vanish. Summability is of norm error bounds.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace LeanPEP.ActualFunction.SummablePerturbation

/-- A finite-prefix expression for the remaining error budget. Its useful
positivity and limit properties explicitly require summability. -/
def errorTail (eps : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑' k, eps k) - ∑ k ∈ Finset.range n, eps k

theorem partial_sum_le_total {eps : ℕ → ℝ}
    (he : ∀ n, 0 ≤ eps n) (hs : Summable eps) (n : ℕ) :
    (∑ k ∈ Finset.range n, eps k) ≤ ∑' k, eps k := by
  have hmono : Monotone (fun n => ∑ k ∈ Finset.range n, eps k) := by
    apply monotone_nat_of_le_succ
    intro k
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (he k)
  exact hmono.ge_of_tendsto hs.hasSum.tendsto_sum_nat n

theorem errorTail_nonneg {eps : ℕ → ℝ}
    (he : ∀ n, 0 ≤ eps n) (hs : Summable eps) (n : ℕ) :
    0 ≤ errorTail eps n :=
  sub_nonneg.mpr (partial_sum_le_total he hs n)

theorem errorTail_succ (eps : ℕ → ℝ) (n : ℕ) :
    errorTail eps (n+1) = errorTail eps n - eps n := by
  simp only [errorTail, Finset.sum_range_succ]
  ring

theorem errorTail_tendsto_zero {eps : ℕ → ℝ} (hs : Summable eps) :
    Tendsto (errorTail eps) atTop (𝓝 0) := by
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∑' k, eps k)
    atTop (𝓝 (∑' k, eps k))).sub hs.hasSum.tendsto_sum_nat
  change Tendsto
    (fun n : ℕ => (∑' k, eps k) - ∑ k ∈ Finset.range n, eps k)
    atTop (𝓝 0)
  simpa only [sub_self] using ht

/-- The exact nonincreasing potential includes the future error tail. -/
theorem corrected_antitone {a eps : ℕ → ℝ}
    (hstep : ∀ n, a (n+1) ≤ a n + eps n) :
    Antitone (fun n => a n + errorTail eps n) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [errorTail_succ]
  linarith only [hstep n]

/-- A nonnegative scalar sequence with summable upward errors has a finite
limit. No monotonicity of the original sequence is asserted. -/
theorem exists_limit_of_summable_error {a eps : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (he : ∀ n, 0 ≤ eps n) (hs : Summable eps)
    (hstep : ∀ n, a (n+1) ≤ a n + eps n) :
    ∃ d : ℝ, Tendsto a atTop (𝓝 d) := by
  let b : ℕ → ℝ := fun n => a n + errorTail eps n
  have hanti : Antitone b := corrected_antitone hstep
  have hb : BddBelow (Set.range b) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact add_nonneg (ha n) (errorTail_nonneg he hs n)
  have hlim := (tendsto_atTop_ciInf hanti hb).sub (errorTail_tendsto_zero hs)
  have hfun : (fun n => b n - errorTail eps n) = a := by
    funext n
    exact add_sub_cancel_right (a n) (errorTail eps n)
  rw [hfun, sub_zero] at hlim
  exact ⟨_, hlim⟩

/-- A uniform bound with the whole summable budget, valid also at time zero. -/
theorem le_initial_add_total {a eps : ℕ → ℝ}
    (he : ∀ n, 0 ≤ eps n) (hs : Summable eps)
    (hstep : ∀ n, a (n+1) ≤ a n + eps n) (n : ℕ) :
    a n ≤ a 0 + ∑' k, eps k := by
  have hpot : a n + errorTail eps n ≤ a 0 + errorTail eps 0 :=
    corrected_antitone hstep (Nat.zero_le n)
  have htail := errorTail_nonneg he hs n
  have hz : errorTail eps 0 = ∑' k, eps k := by
    simp only [errorTail, Finset.range_zero, Finset.sum_empty, sub_zero]
  rw [hz] at hpot
  linarith only [hpot, htail]

section Normed
variable {E : Type*} [NormedAddCommGroup E]

/-- Nonexpansiveness gives additive distance errors around each fixed point. -/
theorem distance_step {T : E → E} {u : ℕ → E} {eps : ℕ → ℝ}
    (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖)
    (herr : ∀ n, ‖u (n+1)-T (u n)‖ ≤ eps n)
    {p : E} (hp : T p = p) (n : ℕ) :
    ‖u (n+1)-p‖ ≤ ‖u n-p‖ + eps n := by
  have ht := dist_triangle (u (n+1)) (T (u n)) p
  simp only [dist_eq_norm] at ht
  have hn := hT (u n) p
  rw [hp] at hn
  linarith only [ht, hn, herr n]

theorem distance_has_limit {T : E → E} {u : ℕ → E} {eps : ℕ → ℝ}
    (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖)
    (hs : Summable eps) (herr : ∀ n, ‖u (n+1)-T (u n)‖ ≤ eps n)
    {p : E} (hp : T p = p) :
    ∃ d : ℝ, Tendsto (fun n => ‖u n-p‖) atTop (𝓝 d) :=
  exists_limit_of_summable_error (fun _ => norm_nonneg _)
    (fun n => (norm_nonneg _).trans (herr n)) hs (distance_step hT herr hp)

theorem distance_le_budget {T : E → E} {u : ℕ → E} {eps : ℕ → ℝ}
    (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖)
    (hs : Summable eps) (herr : ∀ n, ‖u (n+1)-T (u n)‖ ≤ eps n)
    {p : E} (hp : T p = p) (n : ℕ) :
    ‖u n-p‖ ≤ ‖u 0-p‖ + ∑' k, eps k :=
  le_initial_add_total (a := fun k : ℕ => ‖u k-p‖)
    (fun n => (norm_nonneg _).trans (herr n)) hs (distance_step hT herr hp) n

/-- The one-step perturbed energy inequality. The residual is T(u n)-u n,
not u(n+1)-u n; these are different for an inexact orbit. -/
theorem residual_energy_bound {T : E → E} {u : ℕ → E} {eps : ℕ → ℝ}
    {p : E} {c B : ℝ}
    (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖) (hp : T p = p)
    (henergy : ∀ x, ‖T x-p‖^2 + c*‖T x-x‖^2 ≤ ‖x-p‖^2)
    (hB : ∀ n, ‖u n-p‖ ≤ B)
    (herr : ∀ n, ‖u (n+1)-T (u n)‖ ≤ eps n) (n : ℕ) :
    c*‖T (u n)-u n‖^2 ≤
      ‖u n-p‖^2-‖u (n+1)-p‖^2 + 2*B*eps n + (eps n)^2 := by
  have he : 0 ≤ eps n := (norm_nonneg _).trans (herr n)
  have hn := hT (u n) p
  rw [hp] at hn
  have hnb : ‖T (u n)-p‖ ≤ B := hn.trans (hB n)
  have ht := dist_triangle (u (n+1)) (T (u n)) p
  simp only [dist_eq_norm] at ht
  have hnorm : ‖u (n+1)-p‖ ≤ ‖T (u n)-p‖ + eps n := by
    linarith only [ht, herr n]
  have hsq := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) he)).mpr hnorm
  have hprod := mul_le_mul_of_nonneg_left hnb he
  nlinarith only [hsq, hprod, henergy (u n)]

/-- Positive energy margin plus summable norm errors implies vanishing exact
map residual. Boundedness and distance limits are derived, not premises. -/
theorem residual_tendsto_zero {T : E → E} {u : ℕ → E} {eps : ℕ → ℝ}
    {p : E} {c : ℝ} (hc : 0 < c)
    (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖) (hp : T p = p)
    (henergy : ∀ x, ‖T x-p‖^2 + c*‖T x-x‖^2 ≤ ‖x-p‖^2)
    (hs : Summable eps) (herr : ∀ n, ‖u (n+1)-T (u n)‖ ≤ eps n) :
    Tendsto (fun n => ‖T (u n)-u n‖) atTop (𝓝 0) := by
  let B := ‖u 0-p‖ + ∑' k, eps k
  have hB : ∀ n, ‖u n-p‖ ≤ B := distance_le_budget hT hs herr hp
  obtain ⟨d, hd⟩ := distance_has_limit hT hs herr hp
  have hshift : Tendsto (fun n : ℕ => n+1) atTop atTop :=
    (show StrictMono (fun n : ℕ => n+1) from
      fun _ _ hab => Nat.add_lt_add_right hab 1).tendsto_atTop
  have hdnext : Tendsto (fun n => ‖u (n+1)-p‖) atTop (𝓝 d) := hd.comp hshift
  have he0 : Tendsto eps atTop (𝓝 0) := hs.tendsto_atTop_zero
  have hmajor : Tendsto (fun n =>
      (‖u n-p‖^2-‖u (n+1)-p‖^2 + 2*B*eps n + (eps n)^2)/c)
      atTop (𝓝 0) := by
    have ht := ((((hd.pow 2).sub (hdnext.pow 2)).add
      (he0.const_mul (2*B))).add (he0.pow 2)).mul_const c⁻¹
    simpa only [sub_self, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0),
      zero_mul, div_eq_mul_inv] using ht
  have hbound (n : ℕ) : ‖T (u n)-u n‖^2 ≤
      (‖u n-p‖^2-‖u (n+1)-p‖^2 + 2*B*eps n + (eps n)^2)/c := by
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using residual_energy_bound hT hp henergy hB herr n
  have hsq : Tendsto (fun n => ‖T (u n)-u n‖^2) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
      (fun _ => sq_nonneg _) hbound
  have hroot : Tendsto (fun t : ℝ => Real.sqrt t) (𝓝 0) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  have hcomp := hroot.comp hsq
  have hfun : ((fun t : ℝ => Real.sqrt t) ∘ (fun n => ‖T (u n)-u n‖^2)) =
      (fun n => ‖T (u n)-u n‖) := by
    funext n
    exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun] at hcomp
  exact hcomp

/-- Actual adjacent-step norms also vanish. They need not be antitone. -/
theorem step_norm_tendsto_zero {T : E → E} {u : ℕ → E} {eps : ℕ → ℝ}
    (hs : Summable eps) (herr : ∀ n, ‖u (n+1)-T (u n)‖ ≤ eps n)
    (hres : Tendsto (fun n => ‖T (u n)-u n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖u (n+1)-u n‖) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun n => eps n + ‖T (u n)-u n‖) atTop (𝓝 0) := by
    simpa only [add_zero] using hs.tendsto_atTop_zero.add hres
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
    (fun _ => norm_nonneg _)
  intro n
  have ht := dist_triangle (u (n+1)) (T (u n)) (u n)
  simp only [dist_eq_norm] at ht
  exact ht.trans (add_le_add (herr n) (le_refl _))

end Normed
end LeanPEP.ActualFunction.SummablePerturbation
