import LeanPEP.ActualFunction.ProximalExistence
import LeanPEP.ActualFunction.ProximalGradientScaling

/-!
# A selected exact prox map and its actual recursive trajectory

Selection requires a proof that every prox problem has a solution. It never
uses a default point in an infeasible case. This is a noncomputable mathematical
operator, not an executable solver. Under positive L and convexity, C5
uniqueness makes it independent of the existence proof and of any alternative
selector. Finite dimension supplies the existence proof, but the conditional
operator and trajectory results do not require finite dimension.
-/

noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction

namespace ProximalScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Total solvability of the existing prox predicate, supplied as a proposition. -/
def HasProx (L : ℝ≥0) (h : E → ℝ) : Prop := ∀ v, ∃ x, IsProxPoint L h v x

/-- Finite-dimensional whole-space convexity discharges the solvability premise. -/
theorem hasProx_of_finiteDimensional [FiniteDimensional ℝ E] {L : ℝ≥0} {h : E → ℝ}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) : HasProx L h :=
  fun v => exists_isProxPoint hL hh v

/-- Exact choice from proved existence, with no fallback branch. -/
def proxMap {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h) (v : E) : E :=
  Classical.choose (hp v)

theorem proxMap_spec {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h) (v : E) :
    IsProxPoint L h v (proxMap hp v) := Classical.choose_spec (hp v)

/-- Any supplied exact solution is the chosen one. -/
theorem proxMap_eq_of_isProxPoint {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {v x : E}
    (hx : IsProxPoint L h v x) : proxMap hp v = x :=
  isProxPoint_unique hL hh hx (proxMap_spec hp v)

/-- Equality to every exact selector, not just independence of proof arguments. -/
theorem proxMap_eq_of_selector {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (p : E → E) (hspec : ∀ v, IsProxPoint L h v (p v)) : proxMap hp = p := by
  funext v
  exact proxMap_eq_of_isProxPoint hp hL hh (hspec v)

/-- C5 optimality applies to the selected map without an oracle assumption. -/
theorem proxMap_subgradient {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (v : E) :
    Proximal.SubgradientAt h ((L : ℝ) • (v-proxMap hp v)) (proxMap hp v) :=
  subgradient_of_isProxPoint hL hh (proxMap_spec hp v)

end ProximalScaling

namespace ProximalGradientCanonical
open ProximalScaling ProximalGradientScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A single actual infinite trajectory; no horizon is used to choose the map. -/
def iterate {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h) (g : E → E) (x0 : E) : ℕ → E
  | 0 => x0
  | k+1 => proxMap hp (iterate hp g x0 k - (L : ℝ)⁻¹ • g (iterate hp g x0 k))

@[simp] theorem iterate_zero {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (g : E → E) (x0 : E) : iterate hp g x0 0 = x0 := rfl

@[simp] theorem iterate_succ {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (g : E → E) (x0 : E) (k : ℕ) :
    iterate hp g x0 (k+1) =
      proxMap hp (iterate hp g x0 k - (L : ℝ)⁻¹ • g (iterate hp g x0 k)) := rfl

/-- Every finite prefix satisfies the unchanged physical-run contract. -/
theorem iterate_isSmoothProxRun {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (g : E → E) (x0 : E) (N : ℕ) :
    IsSmoothProxRun N L h g (iterate hp g x0) := by
  intro k hk
  exact proxMap_spec hp _

/-- Every other supplied run has the same prefix. This uses only convex h,
positive L and the actual prox conditions, not a smoothness model for g. -/
theorem run_eq_iterate {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    {g : E → E} {x0 : E} {N : ℕ} {x : ℕ → E}
    (hrun : IsSmoothProxRun N L h g x) (hx0 : x 0 = x0)
    (k : ℕ) (hk : k ≤ N) : x k = iterate hp g x0 k := by
  revert hk
  induction k with
  | zero => intro _; exact hx0
  | succ k ih =>
    intro hk
    have hkN : k < N := by omega
    have hxk := ih (by omega)
    have hs := hrun k hkN
    rw [hxk] at hs
    exact (proxMap_eq_of_isProxPoint hp hL hh hs).symm

/-- Conversely, equality of the complete prefix is sufficient for the old run
predicate. Values beyond N are unconstrained, including when N=0. -/
theorem isSmoothProxRun_iff_eq_iterate {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (g : E → E) (x : ℕ → E) (N : ℕ) :
    IsSmoothProxRun N L h g x ↔ ∀ k ≤ N, x k = iterate hp g (x 0) k := by
  constructor
  · intro hrun k hk
    exact run_eq_iterate hp hL hh hrun rfl k hk
  · intro heq k hk
    have hk0 := heq k (by omega)
    have hk1 := heq (k+1) (by omega)
    rw [hk0, hk1]
    exact proxMap_spec hp _

/-- Existence of one trajectory satisfying every finite horizon at once. -/
theorem exists_all_horizons {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (g : E → E) (x0 : E) :
    ∃ x : ℕ → E, x 0 = x0 ∧ ∀ N, IsSmoothProxRun N L h g x :=
  ⟨iterate hp g x0, rfl, iterate_isSmoothProxRun hp g x0⟩

/-- The concrete finite-dimensional algorithm has no external solvability
argument. Convexity and positive L prove it for every input. -/
def finiteDimensionalIterate [FiniteDimensional ℝ E] (L : ℝ≥0) (h : E → ℝ)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (g : E → E) (x0 : E) : ℕ → E :=
  iterate (hasProx_of_finiteDimensional hL hh) g x0

@[simp] theorem finiteDimensionalIterate_zero [FiniteDimensional ℝ E]
    (L : ℝ≥0) (h : E → ℝ) (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (g : E → E) (x0 : E) : finiteDimensionalIterate L h hL hh g x0 0 = x0 := rfl

theorem finiteDimensionalIterate_isSmoothProxRun [FiniteDimensional ℝ E]
    (L : ℝ≥0) (h : E → ℝ) (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (g : E → E) (x0 : E) (N : ℕ) :
    IsSmoothProxRun N L h g (finiteDimensionalIterate L h hL hh g x0) :=
  iterate_isSmoothProxRun (hasProx_of_finiteDimensional hL hh) g x0 N

theorem exists_all_horizons_finiteDimensional [FiniteDimensional ℝ E]
    {L : ℝ≥0} {h : E → ℝ} (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (g : E → E) (x0 : E) :
    ∃ x : ℕ → E, x 0 = x0 ∧ ∀ N, IsSmoothProxRun N L h g x :=
  exists_all_horizons (hasProx_of_finiteDimensional hL hh) g x0

end ProximalGradientCanonical
end LeanPEP.ActualFunction
