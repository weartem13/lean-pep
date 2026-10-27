import LeanPEP.GramPEP.ExplicitConstraints

/-!
# Component-local smooth and nonsmooth interpolation compiler

The value dimension counts VALUE SLOTS, not one homogeneous set of samples.
Each component carries its own sample list and class. Ordered constraints are
compiled only WITHIN each component. All components share a Gram basis.

`ModelQ` is reused as an explicit-constraint carrier: its dummy position and
gradient fields are deliberately zero, not actual smooth samples. Every
function-class inequality is in `assumptions`; certificates must have empty
`interpTerms`. `checkUpperCertQ_sound_real_explicit` supplies the sound rule.
-/

namespace LeanPEP.Profiles.Composite

open LeanPEP.GramPEP

inductive FunctionClassQ where
  | convex
  | oneSmoothConvex
  deriving DecidableEq, Repr

/-- A function-value slot with a position and an oracle vector. -/
structure SampleQ (p m : ℕ) where
  valueIndex : Fin p
  position : VecExpr m ℚ
  oracle : VecExpr m ℚ

/-- One function component, with no cross-component interpolation. -/
structure ComponentQ (p m : ℕ) where
  functionClass : FunctionClassQ
  samples : List (SampleQ p m)

/-- Convex support inequality, optionally strengthened by the unit-smooth
squared-gradient term. Orientation is always `value_i - value_j - ...`. -/
def interpolationExprQ {p m : ℕ} (kind : FunctionClassQ)
    (a b : SampleQ p m) : LinearExprQ p m :=
  let support := LinearExprQ.sub
    (LinearExprQ.sub (LinearExprQ.valueVar a.valueIndex)
      (LinearExprQ.valueVar b.valueIndex))
    (LinearExprQ.gramBilinear b.oracle (a.position - b.position))
  match kind with
  | .convex => support
  | .oneSmoothConvex => LinearExprQ.sub support
      (LinearExprQ.scale (1/2) (LinearExprQ.gramNorm (a.oracle - b.oracle)))

/-- Deterministic row-major order within one function component. -/
def componentConstraintsQ {p m : ℕ} (c : ComponentQ p m) :
    List (LinearExprQ p m) :=
  c.samples.flatMap (fun a => c.samples.map (fun b =>
    interpolationExprQ c.functionClass a b))

structure ProfileQ (p m : ℕ) where
  components : List (ComponentQ p m)
  assumptions : List (LinearExprQ p m)
  objective : LinearExprQ p m

def compileConstraintsQ {p m : ℕ} (profile : ProfileQ p m) :
    List (LinearExprQ p m) :=
  profile.components.flatMap componentConstraintsQ ++ profile.assumptions

/-- Existing `ModelQ`, used ONLY with the explicit-constraint soundness rule. -/
def compileModelQ {p m : ℕ} (profile : ProfileQ p m) : ModelQ p m :=
  { position := fun _ => 0
    gradient := fun _ => 0
    assumptions := compileConstraintsQ profile }

/-- Convex component evaluation contains no smooth gradient-square penalty. -/
theorem evalR_interpolationExprQ_convex {p m : ℕ}
    (a b : SampleQ p m) (d : DataR (Fin p) m)
    (hG : IsGramSymmetric d.gram) :
    (interpolationExprQ .convex a b).evalR d =
      d.value a.valueIndex - d.value b.valueIndex -
        gramInner d.gram (castVecQ b.oracle)
          (castVecQ (a.position - b.position)) := by
  simp [interpolationExprQ, LinearExprQ.evalR_gramBilinear _ _ d hG]

/-- Unit-smooth component evaluation uses that SAME component's oracle
values and value slots, never those of another component. -/
theorem evalR_interpolationExprQ_smooth {p m : ℕ}
    (a b : SampleQ p m) (d : DataR (Fin p) m)
    (hG : IsGramSymmetric d.gram) :
    (interpolationExprQ .oneSmoothConvex a b).evalR d =
      d.value a.valueIndex - d.value b.valueIndex -
        gramInner d.gram (castVecQ b.oracle)
          (castVecQ (a.position - b.position)) -
        (1/2 : ℝ) * gramNormSq d.gram (castVecQ (a.oracle - b.oracle)) := by
  simp [interpolationExprQ, LinearExprQ.evalR_gramBilinear _ _ d hG,
    LinearExprQ.evalR_gramNorm _ d hG]

/-- A component-local feasibility proof covers every compiled pair, including
self pairs. This is a soundness statement, not interpolation completeness. -/
theorem componentConstraintsQ_nonneg {p m : ℕ}
    (c : ComponentQ p m) (d : DataR (Fin p) m)
    (hc : ∀ a ∈ c.samples, ∀ b ∈ c.samples,
      0 ≤ (interpolationExprQ c.functionClass a b).evalR d) :
    ∀ e ∈ componentConstraintsQ c, 0 ≤ e.evalR d := by
  intro e he
  rcases List.mem_flatMap.mp he with ⟨a, ha, he⟩
  rcases List.mem_map.mp he with ⟨b, hb, rfl⟩
  exact hc a ha b hb

/-- All compiled constraints are justified component by component. -/
theorem compileModelQ_feasible {p m : ℕ} (profile : ProfileQ p m)
    (d : DataR (Fin p) m)
    (hcomponents : ∀ c ∈ profile.components, ∀ a ∈ c.samples,
      ∀ b ∈ c.samples, 0 ≤ (interpolationExprQ c.functionClass a b).evalR d)
    (hassumptions : ∀ e ∈ profile.assumptions, 0 ≤ e.evalR d) :
    AssumptionsFeasibleR (compileModelQ profile) d := by
  intro k
  have hk := List.get_mem (compileModelQ profile).assumptions k
  change (compileConstraintsQ profile).get k ∈
    profile.components.flatMap componentConstraintsQ ++ profile.assumptions at hk
  rcases List.mem_append.mp hk with hc | ha
  · rcases List.mem_flatMap.mp hc with ⟨c, hc, he⟩
    exact componentConstraintsQ_nonneg c d (hcomponents c hc) _ he
  · exact hassumptions _ ha

/-- The generic compiler feeds the original checker. The objective and
empty-interpolation conditions are explicit and cannot be dropped. -/
theorem certificate_upper {p m : ℕ} (profile : ProfileQ p m)
    (c : UpperCertQ (compileModelQ profile))
    (hcheck : checkUpperCertQ c = true) (hempty : c.interpTerms = [])
    (hobjective : c.objective = profile.objective)
    (d : DataR (Fin p) m) (hpsd : IsGramPosSemidef d.gram)
    (hconstraints : AssumptionsFeasibleR (compileModelQ profile) d) :
    profile.objective.evalR d ≤ (c.bound : ℝ) := by
  rw [← hobjective]
  exact checkUpperCertQ_sound_real_explicit c hcheck hempty d hpsd hconstraints

end LeanPEP.Profiles.Composite
