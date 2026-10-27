import LeanPEP.Adapters.ProximalGradientSource
import LeanPEP.GramPEP.OriginCoordinates

/-!
# D3: uncentered exact composite snapshots with checked origin elimination

This profile uses the explicit normalized leaf order
`[x_star,x0,g_star,g0,...,gT,s1,...,sT]`. It is not an arbitrary PEPit
leaf-order adapter, a live capture, or a proof about JSON bytes.

The forward map and zero-origin section are checked independently. Merely
matching the restriction to x_star=0 is insufficient: sample, constraint and
objective round trips must reconstruct the submitted native arrays in full.
Certificates are checked in BOTH dimensions by the unchanged upper checker;
we do not assert a new completeness theorem for certificate transformation.
-/

namespace LeanPEP.Adapters.ProximalGradientCoordinates

open LeanPEP.GramPEP LeanPEP.Profiles
open LeanPEP.GramPEP.OriginCoordinates
open LeanPEP.Adapters.ExactFormulation

abbrev leafCount (n : ℕ) := ProximalGradient.basisCount n + 1

/-- Compare every entry, including both rectangular dimensions. -/
def checkRectQ {r c : ℕ} (A B : Matrix (Fin r) (Fin c) ℚ) : Bool :=
  (List.finRange r).all (fun i => checkVecExprEqQ (A i) (B i))

theorem checkRectQ_eq_true_iff {r c : ℕ} (A B : Matrix (Fin r) (Fin c) ℚ) :
    checkRectQ A B = true ↔ A = B := by
  simp only [checkRectQ, List.all_eq_true, checkVecExprEqQ_eq_true_iff]
  constructor
  · intro h
    funext i
    exact h i (by simp)
  · intro h
    subst B
    intro i hi
    rfl

@[ext] structure SourceQ (n : ℕ) where
  header : ProximalGradientSource.HeaderQ
  centerMatrix : Matrix (Fin (ProximalGradient.basisCount n)) (Fin (leafCount n)) ℚ
  sectionMatrix : Matrix (Fin (leafCount n)) (Fin (ProximalGradient.basisCount n)) ℚ
  smoothSamples : List (Composite.SampleQ (ProximalGradient.valueCount n) (leafCount n))
  nonsmoothSamples : List (Composite.SampleQ (ProximalGradient.valueCount n) (leafCount n))
  constraints : List (LinearExprQ (ProximalGradient.valueCount n) (leafCount n))
  objective : LinearExprQ (ProximalGradient.valueCount n) (leafCount n)

def SourceQ.model {n : ℕ} (s : SourceQ n) :
    ModelQ (ProximalGradient.valueCount n) (leafCount n) :=
  { position := fun _ => 0, gradient := fun _ => 0, assumptions := s.constraints }

def expectedHeaderQ (n : ℕ) : ProximalGradientSource.HeaderQ :=
  { ProximalGradientSource.expectedHeaderQ n with
    coordinates := "uncentered-xstar-x0-gstar-gradients-residuals-v1"
    basisCount := leafCount n
    basisOrder := "x_star" :: "x0" :: (ProximalGradientSource.expectedHeaderQ n).basisOrder.tail }

/-- Normalize only coordinate metadata. The ORIGINAL native header is separately
compared in full, so wrong horizon, order, scale, class or sense cannot be hidden. -/
def centeredSourceQ {n : ℕ} (s : SourceQ n) : ProximalGradientSource.SourceQ n :=
  { header :=
      { s.header with
        coordinates := (ProximalGradientSource.expectedHeaderQ n).coordinates
        basisCount := ProximalGradient.basisCount n
        basisOrder := (ProximalGradientSource.expectedHeaderQ n).basisOrder }
    smoothSamples := s.smoothSamples.map restrictSampleQ
    nonsmoothSamples := s.nonsmoothSamples.map restrictSampleQ
    constraints := s.constraints.map restrictExprQ
    objective := restrictExprQ s.objective }

/-- Built only from the old Lean compiler; never from producer-supplied arrays. -/
def expectedSourceQ (n : ℕ) : SourceQ n :=
  let e := ProximalGradientSource.expectedSourceQ n
  let a := ProximalGradient.initialBasisIndex n
  { header := expectedHeaderQ n
    centerMatrix := centerMapQ a
    sectionMatrix := sectionMapQ (ProximalGradient.basisCount n)
    smoothSamples := e.smoothSamples.map (liftSampleQ a)
    nonsmoothSamples := e.nonsmoothSamples.map (liftSampleQ a)
    constraints := e.constraints.map (liftExprQ a)
    objective := liftExprQ a e.objective }

structure AuditQ where
  headerOK : Bool
  centerMatrixOK : Bool
  sectionMatrixOK : Bool
  smoothRoundtripOK : Bool
  nonsmoothRoundtripOK : Bool
  constraintsRoundtripOK : Bool
  objectiveRoundtripOK : Bool
  centeredSourceOK : Bool
  deriving DecidableEq, Repr

def auditSourceQ {n : ℕ} (s : SourceQ n) : AuditQ :=
  let t := centeredSourceQ s
  let a := ProximalGradient.initialBasisIndex n
  { headerOK := decide (s.header = expectedHeaderQ n)
    centerMatrixOK := checkRectQ s.centerMatrix (centerMapQ a)
    sectionMatrixOK := checkRectQ s.sectionMatrix (sectionMapQ (ProximalGradient.basisCount n))
    smoothRoundtripOK := checkListQ ProximalGradientSource.checkSampleQ
      s.smoothSamples (t.smoothSamples.map (liftSampleQ a))
    nonsmoothRoundtripOK := checkListQ ProximalGradientSource.checkSampleQ
      s.nonsmoothSamples (t.nonsmoothSamples.map (liftSampleQ a))
    constraintsRoundtripOK := checkListQ checkLinearExprEqQ
      s.constraints (t.constraints.map (liftExprQ a))
    objectiveRoundtripOK := checkLinearExprEqQ s.objective (liftExprQ a t.objective)
    centeredSourceOK := ProximalGradientSource.checkSourceQ t }

def checkSourceQ {n : ℕ} (s : SourceQ n) : Bool :=
  let a := auditSourceQ s
  a.headerOK && (a.centerMatrixOK && (a.sectionMatrixOK &&
    (a.smoothRoundtripOK && (a.nonsmoothRoundtripOK &&
      (a.constraintsRoundtripOK && (a.objectiveRoundtripOK && a.centeredSourceOK))))))

theorem checkSourceQ_eq_true_iff {n : ℕ} (s : SourceQ n) :
    checkSourceQ s = true ↔
      s.header = expectedHeaderQ n ∧
      s.centerMatrix = centerMapQ (ProximalGradient.initialBasisIndex n) ∧
      s.sectionMatrix = sectionMapQ (ProximalGradient.basisCount n) ∧
      s.smoothSamples = (centeredSourceQ s).smoothSamples.map
        (liftSampleQ (ProximalGradient.initialBasisIndex n)) ∧
      s.nonsmoothSamples = (centeredSourceQ s).nonsmoothSamples.map
        (liftSampleQ (ProximalGradient.initialBasisIndex n)) ∧
      s.constraints = (centeredSourceQ s).constraints.map
        (liftExprQ (ProximalGradient.initialBasisIndex n)) ∧
      s.objective = liftExprQ (ProximalGradient.initialBasisIndex n) (centeredSourceQ s).objective ∧
      ProximalGradientSource.checkSourceQ (centeredSourceQ s) = true := by
  simp only [checkSourceQ, auditSourceQ, Bool.and_eq_true, decide_eq_true_eq,
    checkRectQ_eq_true_iff,
    checkListQ_eq_true_iff ProximalGradientSource.checkSampleQ
      ProximalGradientSource.checkSampleQ_eq_true_iff,
    checkListQ_eq_true_iff checkLinearExprEqQ checkLinearExprEqQ_eq_true_iff,
    checkLinearExprEqQ_eq_true_iff]

/-- Full native equality, not merely equality after erasing origin coordinates. -/
theorem checkSourceQ_sound {n : ℕ} (s : SourceQ n) (hs : checkSourceQ s = true) :
    s = expectedSourceQ n := by
  rcases (checkSourceQ_eq_true_iff s).mp hs with ⟨hh, hC, hJ, hf, hg, hc, ho, ht⟩
  have he := (ProximalGradientSource.checkSourceQ_eq_true_iff (centeredSourceQ s)).mp ht
  rw [he] at hf hg hc ho
  exact SourceQ.ext hh hC hJ hf hg hc ho

/-- Restricting the canonical lifted source recovers the OLD centered source. -/
theorem centered_expectedSourceQ (n : ℕ) :
    centeredSourceQ (expectedSourceQ n) = ProximalGradientSource.expectedSourceQ n := by
  apply ProximalGradientSource.SourceQ.ext
  · rfl
  · simp [centeredSourceQ, expectedSourceQ, List.map_map, Function.comp_def]
  · simp [centeredSourceQ, expectedSourceQ, List.map_map, Function.comp_def]
  · simp [centeredSourceQ, expectedSourceQ, List.map_map, Function.comp_def]
  · exact restrict_liftExprQ _ _

theorem expectedSource_check (n : ℕ) : checkSourceQ (expectedSourceQ n) = true := by
  apply (checkSourceQ_eq_true_iff (expectedSourceQ n)).mpr
  rw [centered_expectedSourceQ]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ProximalGradientSource.expectedSource_check n⟩

/-- Exact equality of the entire native source, in both directions. -/
theorem checkSourceQ_eq_expected {n : ℕ} (s : SourceQ n) :
    checkSourceQ s = true ↔ s = expectedSourceQ n := by
  constructor
  · exact checkSourceQ_sound s
  · intro h
    subst s
    exact expectedSource_check n

/-- Index transport uses proved list-map length equality; no default/zip lookup. -/
def centeredAssumptionQ {n : ℕ} (s : SourceQ n) (t : AssumptionTermQ s.model) :
    AssumptionTermQ (centeredSourceQ s).model :=
  { weight := t.weight
    index := ⟨t.index.val, by
      simpa only [ProximalGradientSource.SourceQ.model, centeredSourceQ, SourceQ.model,
        List.length_map] using t.index.isLt⟩ }

/-- Restrict the submitted certificate, preserving bound, every weight, index
and implicit term. No factor synthesis, reordering or coefficient repair here. -/
def centeredUpperQ {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) :
    UpperCertQ (centeredSourceQ s).model :=
  { bound := c.bound
    objective := restrictExprQ c.objective
    interpTerms := c.interpTerms
    assumptionTerms := c.assumptionTerms.map (centeredAssumptionQ s)
    dualMatrix := restrictGram c.dualMatrix
    dualFactor := restrictPSDFactorQ c.dualFactor }

@[simp] theorem centeredUpper_bound {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) :
    (centeredUpperQ s c).bound = c.bound := rfl

/-- Both complete old checks are required. A malformed native certificate cannot
hide in coordinates removed by the zero-origin section. -/
def checkBoundQ {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) : Bool :=
  checkSourceQ s && (checkUpperCertQ c && (decide (c.interpTerms = []) &&
    (checkLinearExprEqQ c.objective s.objective &&
      ProximalGradientSource.checkBoundQ (centeredSourceQ s) (centeredUpperQ s c))))

theorem checkBoundQ_eq_true_iff {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) :
    checkBoundQ s c = true ↔ checkSourceQ s = true ∧ checkUpperCertQ c = true ∧
      c.interpTerms = [] ∧ c.objective = s.objective ∧
      ProximalGradientSource.checkBoundQ (centeredSourceQ s) (centeredUpperQ s c) = true := by
  simp only [checkBoundQ, Bool.and_eq_true, decide_eq_true_eq, checkLinearExprEqQ_eq_true_iff]

/-- D2's independently bound certificate, with the SAME submitted bound. -/
theorem checked_certificate {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model)
    (hc : checkBoundQ s c = true) :
    ∃ d : UpperCertQ (ProximalGradient.modelQ n),
      checkUpperCertQ d = true ∧ d.interpTerms = [] ∧
      d.objective = ProximalGradient.objectiveQ n ∧ d.bound = c.bound := by
  have ht := ((checkBoundQ_eq_true_iff s c).mp hc).2.2.2.2
  obtain ⟨d, hd, hi, ho, hb⟩ :=
    ProximalGradientSource.checked_certificate (centeredSourceQ s) (centeredUpperQ s c) ht
  exact ⟨d, hd, hi, ho, hb⟩

end LeanPEP.Adapters.ProximalGradientCoordinates
