import LeanPEP.ActualFunction.AnalyticBridge

/-!
# Real-valued convex subgradient and normalized proximal optimality

The scope is real-valued functions on real inner-product spaces. There is no
extended-real domain, no proximal-existence theorem and no selected prox map.
`IsUnitProxPoint` is an actual global minimization property, not a synonym for
a formal update. We prove its equivalence to the subgradient residual under
convexity. The unit coefficient is the normalized step used in v0.13C1.
-/

noncomputable section
namespace LeanPEP.ActualFunction.Proximal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Global supporting-hyperplane definition; no differentiability is required. -/
def SubgradientAt (h : E → ℝ) (s x : E) : Prop :=
  ∀ y, h x + inner ℝ s (y - x) ≤ h y

/-- The ordinary unit-step prox minimization problem. -/
def IsUnitProxPoint (h : E → ℝ) (v x : E) : Prop :=
  ∀ y, h x + (1/2 : ℝ) * inner ℝ (x - v) (x - v) ≤
    h y + (1/2 : ℝ) * inner ℝ (y - v) (y - v)

theorem isUnitProxPoint_iff_norm (h : E → ℝ) (v x : E) :
    IsUnitProxPoint h v x ↔
      ∀ y, h x + (1/2 : ℝ) * ‖x - v‖ ^ 2 ≤
        h y + (1/2 : ℝ) * ‖y - v‖ ^ 2 := by
  simp only [IsUnitProxPoint, real_inner_self_eq_norm_sq]

/-- Exact quadratic remainder for proximal optimality. -/
theorem quadratic_remainder (v x y : E) :
    (1/2 : ℝ) * inner ℝ (y - v) (y - v) -
        (1/2 : ℝ) * inner ℝ (x - v) (x - v) +
        inner ℝ (v - x) (y - x) =
      (1/2 : ℝ) * inner ℝ (y - x) (y - x) := by
  simp only [inner_sub_left, inner_sub_right, real_inner_comm]
  ring

/-- Subgradient optimality implies actual global proximal minimality. -/
theorem isUnitProxPoint_of_subgradient {h : E → ℝ} {v x : E}
    (hs : SubgradientAt h (v - x) x) : IsUnitProxPoint h v x := by
  intro y
  have hsupport := hs y
  have hquad := quadratic_remainder v x y
  have hnonneg : 0 ≤ inner ℝ (y - x) (y - x) := real_inner_self_nonneg
  linarith

/-- A nonnegative quadratic on every sufficiently short positive segment has
nonnegative linear coefficient. The proof chooses one explicit rational
expression in the coefficients; it does not appeal to a limiting oracle. -/
private theorem linear_nonneg_of_segment_quadratic {a b : ℝ}
    (hb : 0 ≤ b)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ t * a + t ^ 2 * b) : 0 ≤ a := by
  by_contra ha
  have ha : a < 0 := lt_of_not_ge ha
  have hd : 0 < b - a := by linarith
  let t : ℝ := (-a) / (b - a)
  have ht : 0 < t := div_pos (neg_pos.mpr ha) hd
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ hd).2
    linarith
  have hrel : t * (b - a) = -a := by
    dsimp [t]
    field_simp [ne_of_gt hd]
  have hi : a + t * b < 0 := by
    nlinarith [mul_neg_of_pos_of_neg ht ha]
  have hneg := mul_neg_of_pos_of_neg ht hi
  have hpos := h t ht ht1
  nlinarith

/-- The converse uses convexity along the segment from the minimizer to an
arbitrary comparison point. No finite-dimensionality or prox existence is used. -/
theorem subgradient_of_isUnitProxPoint {h : E → ℝ} {v x : E}
    (hh : ConvexOn ℝ Set.univ h) (hp : IsUnitProxPoint h v x) :
    SubgradientAt h (v - x) x := by
  intro y
  have hlinear : 0 ≤ h y - h x - inner ℝ (v - x) (y - x) := by
    apply linear_nonneg_of_segment_quadratic
      (b := (1/2 : ℝ) * inner ℝ (y - x) (y - x))
    · exact mul_nonneg (by norm_num) real_inner_self_nonneg
    · intro t ht ht1
      have hz : (1 - t) • x + t • y = x + t • (y - x) := by
        simp only [sub_smul, one_smul, smul_sub]
        abel
      have hc := hh.2 (show x ∈ Set.univ from trivial)
        (show y ∈ Set.univ from trivial) (show 0 ≤ 1 - t by linarith)
        (le_of_lt ht) (show 1 - t + t = 1 by ring)
      rw [hz] at hc
      simp only [smul_eq_mul] at hc
      have hp' := hp (x + t • (y - x))
      have hquad :
          (1/2 : ℝ) * inner ℝ ((x + t • (y - x)) - v) ((x + t • (y - x)) - v) -
            (1/2 : ℝ) * inner ℝ (x - v) (x - v) =
          -t * inner ℝ (v - x) (y - x) +
            t ^ 2 * ((1/2 : ℝ) * inner ℝ (y - x) (y - x)) := by
        simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
          real_inner_smul_left, real_inner_smul_right, real_inner_comm]
        ring
      nlinarith [hc, hp', hquad]
  linarith

theorem isUnitProxPoint_iff_subgradient {h : E → ℝ} {v x : E}
    (hh : ConvexOn ℝ Set.univ h) :
    IsUnitProxPoint h v x ↔ SubgradientAt h (v - x) x :=
  ⟨subgradient_of_isUnitProxPoint hh, isUnitProxPoint_of_subgradient⟩

/-- The implicit proximal-gradient update and its residual subgradient. -/
structure IsUnitForwardBackwardStep (h : E → ℝ) (g0 x0 x1 s1 : E) : Prop where
  subgradient : SubgradientAt h s1 x1
  update : x1 = x0 - g0 - s1

/-- An actual prox minimizer supplies exactly the oracle/update contract
compiled into the composite Gram model. -/
theorem forwardBackwardStep_of_prox {h : E → ℝ} {g0 x0 x1 : E}
    (hh : ConvexOn ℝ Set.univ h) (hp : IsUnitProxPoint h (x0 - g0) x1) :
    IsUnitForwardBackwardStep h g0 x0 x1 (x0 - g0 - x1) := by
  refine ⟨subgradient_of_isUnitProxPoint hh hp, ?_⟩
  abel

theorem IsUnitForwardBackwardStep.prox {h : E → ℝ} {g0 x0 x1 s1 : E}
    (hstep : IsUnitForwardBackwardStep h g0 x0 x1 s1) :
    IsUnitProxPoint h (x0 - g0) x1 := by
  apply isUnitProxPoint_of_subgradient
  have hs : x0 - g0 - x1 = s1 := by rw [hstep.update]; abel
  rw [hs]
  exact hstep.subgradient

/-- Composite stationarity means cancellation, not separate stationarity. -/
theorem composite_globalMin {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsOneSmoothConvexFirstOrder f g)
    (hs : SubgradientAt h (-g xStar) xStar) (y : E) :
    f xStar + h xStar ≤ f y + h y := by
  have h1 := hf.lowerModel xStar y
  have h2 := hs y
  simp only [inner_neg_left] at h2
  linarith

end LeanPEP.ActualFunction.Proximal
