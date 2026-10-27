import LeanPEP.Adapters.ExactFormulation
import LeanPEP.Profiles.ProximalGradient

/-!
# D2: centered exact composite source snapshots bound to the old PG compiler

The supported boundary is normalized (L = step = radius^2 = 1) and already in
C2's centered basis. It is NOT a PEPit-native leaf-basis adapter, a coordinate
transformation proof, a live capture, or producer authentication. All source
arrays remain untrusted. The expected arrays come solely from the old Lean
profile/compiler, never from the producer's copy of the model.

Value slots belong to two separate components. The model's dummy position and
gradient fields remain zero; all component interpolation lives in explicit
assumptions. Consequently the empty-implicit-interpolation guard is mandatory.
-/

namespace LeanPEP.Adapters.ProximalGradientSource

open LeanPEP.GramPEP LeanPEP.Profiles
open LeanPEP.Adapters.ExactFormulation

inductive SenseQ where
  | geZero
  | leZero
  deriving DecidableEq, Repr

inductive RowKindQ where
  | smoothPair
  | convexPair
  | radius
  deriving DecidableEq, Repr

structure RowTagQ where
  kind : RowKindQ
  i : Option Nat
  j : Option Nat
  deriving DecidableEq, Repr

/-- Mathematical convention and ordered identifiers, not provenance claims. -/
structure HeaderQ where
  profileId : String
  coordinates : String
  steps : Nat
  valueCount : Nat
  basisCount : Nat
  smoothness : ℚ
  stepSize : ℚ
  radiusSquared : ℚ
  smoothClass : Composite.FunctionClassQ
  nonsmoothClass : Composite.FunctionClassQ
  sense : SenseQ
  basisOrder : List String
  valueOrder : List String
  constraintOrder : List RowTagQ
  deriving DecidableEq, Repr

/-- `n` retains C2's convention: the actual positive horizon is T = n+1. -/
@[ext] structure SourceQ (n : ℕ) where
  header : HeaderQ
  smoothSamples : List (Composite.SampleQ (ProximalGradient.valueCount n) (ProximalGradient.basisCount n))
  nonsmoothSamples : List (Composite.SampleQ (ProximalGradient.valueCount n) (ProximalGradient.basisCount n))
  constraints : List (LinearExprQ (ProximalGradient.valueCount n) (ProximalGradient.basisCount n))
  objective : LinearExprQ (ProximalGradient.valueCount n) (ProximalGradient.basisCount n)

/-- The producer's constraint list, not the expected one, forms its carrier. -/
def SourceQ.model {n : ℕ} (s : SourceQ n) :
    ModelQ (ProximalGradient.valueCount n) (ProximalGradient.basisCount n) :=
  { position := fun _ => 0
    gradient := fun _ => 0
    assumptions := s.constraints }

def pairTags (kind : RowKindQ) (k : ℕ) : List RowTagQ :=
  (List.range k).flatMap fun i => (List.range k).map fun j =>
    { kind := kind, i := some i, j := some j }

def expectedHeaderQ (n : ℕ) : HeaderQ :=
  { profileId := "proximal-gradient-unit-positive-horizon-v1"
    coordinates := "centered-x0-gstar-gradients-residuals-v1"
    steps := n + 1
    valueCount := ProximalGradient.valueCount n
    basisCount := ProximalGradient.basisCount n
    smoothness := 1
    stepSize := 1
    radiusSquared := 1
    smoothClass := .oneSmoothConvex
    nonsmoothClass := .convex
    sense := .geZero
    basisOrder := ["x0-x_star", "g_star"] ++
      ((List.range (n+2)).map fun k => "g" ++ toString k) ++
      ((List.range (n+1)).map fun k => "s" ++ toString (k+1))
    valueOrder := ["f_star"] ++
      ((List.range (n+2)).map fun k => "f" ++ toString k) ++ ["h_star"] ++
      ((List.range (n+1)).map fun k => "h" ++ toString (k+1))
    constraintOrder := pairTags .smoothPair (n+3) ++ pairTags .convexPair (n+2) ++
      [{ kind := .radius, i := none, j := none }] }

/-- All mathematical expected data are independently built by the old C2 code. -/
def expectedSourceQ (n : ℕ) : SourceQ n :=
  { header := expectedHeaderQ n
    smoothSamples := (ProximalGradient.smoothComponentQ n).samples
    nonsmoothSamples := (ProximalGradient.nonsmoothComponentQ n).samples
    constraints := (ProximalGradient.modelQ n).assumptions
    objective := ProximalGradient.objectiveQ n }

/-- No new model is silently substituted: the expected carrier IS the old model. -/
theorem expectedSource_model (n : ℕ) :
    (expectedSourceQ n).model = ProximalGradient.modelQ n := rfl

def checkSampleQ {p m : ℕ} (a b : Composite.SampleQ p m) : Bool :=
  decide (a.valueIndex = b.valueIndex) &&
    (checkVecExprEqQ a.position b.position && checkVecExprEqQ a.oracle b.oracle)

theorem checkSampleQ_eq_true_iff {p m : ℕ} (a b : Composite.SampleQ p m) :
    checkSampleQ a b = true ↔ a = b := by
  cases a
  cases b
  simp only [checkSampleQ, Bool.and_eq_true, decide_eq_true_eq,
    checkVecExprEqQ_eq_true_iff, Composite.SampleQ.mk.injEq]

/-- Block diagnostics are independent of the mathematical certificate checks. -/
structure AuditQ where
  headerOK : Bool
  smoothSamplesOK : Bool
  nonsmoothSamplesOK : Bool
  constraintsOK : Bool
  objectiveOK : Bool
  deriving DecidableEq, Repr

def auditSourceQ {n : ℕ} (s : SourceQ n) : AuditQ :=
  let e := expectedSourceQ n
  { headerOK := decide (s.header = e.header)
    smoothSamplesOK := checkListQ checkSampleQ s.smoothSamples e.smoothSamples
    nonsmoothSamplesOK := checkListQ checkSampleQ s.nonsmoothSamples e.nonsmoothSamples
    constraintsOK := checkListQ checkLinearExprEqQ s.constraints e.constraints
    objectiveOK := checkLinearExprEqQ s.objective e.objective }

def checkSourceQ {n : ℕ} (s : SourceQ n) : Bool :=
  let a := auditSourceQ s
  a.headerOK && (a.smoothSamplesOK && (a.nonsmoothSamplesOK &&
    (a.constraintsOK && a.objectiveOK)))

/-- Full source equality, including order and list lengths, not hash equality. -/
theorem checkSourceQ_eq_true_iff {n : ℕ} (s : SourceQ n) :
    checkSourceQ s = true ↔ s = expectedSourceQ n := by
  have hp : checkSourceQ s = true ↔
      s.header = (expectedSourceQ n).header ∧
      s.smoothSamples = (expectedSourceQ n).smoothSamples ∧
      s.nonsmoothSamples = (expectedSourceQ n).nonsmoothSamples ∧
      s.constraints = (expectedSourceQ n).constraints ∧
      s.objective = (expectedSourceQ n).objective := by
    simp only [checkSourceQ, auditSourceQ, Bool.and_eq_true, decide_eq_true_eq,
      checkListQ_eq_true_iff checkSampleQ checkSampleQ_eq_true_iff,
      checkListQ_eq_true_iff checkLinearExprEqQ checkLinearExprEqQ_eq_true_iff,
      checkLinearExprEqQ_eq_true_iff]
  constructor
  · intro h
    rcases hp.mp h with ⟨hh, hsm, hns, hc, ho⟩
    exact SourceQ.ext hh hsm hns hc ho
  · intro h
    apply hp.mpr
    subst s
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem expectedSource_check (n : ℕ) : checkSourceQ (expectedSourceQ n) = true :=
  (checkSourceQ_eq_true_iff _).mpr rfl

theorem source_model_eq {n : ℕ} (s : SourceQ n) (hs : checkSourceQ s = true) :
    s.model = ProximalGradient.modelQ n := by
  rw [(checkSourceQ_eq_true_iff s).mp hs]
  exact expectedSource_model n

theorem source_objective_eq {n : ℕ} (s : SourceQ n) (hs : checkSourceQ s = true) :
    s.objective = ProximalGradient.objectiveQ n := by
  rw [(checkSourceQ_eq_true_iff s).mp hs]
  rfl

/-- A certificate is first checked against the SOURCE'S own model. Source
binding, empty implicit interpolation and objective equality are separate guards. -/
def checkBoundQ {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) : Bool :=
  checkSourceQ s && (checkUpperCertQ c &&
    (decide (c.interpTerms = []) && checkLinearExprEqQ c.objective s.objective))

theorem checkBoundQ_eq_true_iff {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) :
    checkBoundQ s c = true ↔ checkSourceQ s = true ∧ checkUpperCertQ c = true ∧
      c.interpTerms = [] ∧ c.objective = s.objective := by
  simp only [checkBoundQ, Bool.and_eq_true, decide_eq_true_eq,
    checkLinearExprEqQ_eq_true_iff]

/-- Acceptance produces an accepted certificate of the OLD expected model,
with exactly the submitted bound and the original composite objective. -/
theorem checked_certificate {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model)
    (hc : checkBoundQ s c = true) :
    ∃ d : UpperCertQ (ProximalGradient.modelQ n),
      checkUpperCertQ d = true ∧ d.interpTerms = [] ∧
      d.objective = ProximalGradient.objectiveQ n ∧ d.bound = c.bound := by
  rcases (checkBoundQ_eq_true_iff s c).mp hc with ⟨hs, hu, hi, ho⟩
  let hm := source_model_eq s hs
  refine ⟨c.rebind hm, ?_, ?_, ?_, ?_⟩
  · rw [checkUpperCertQ_rebind]
    exact hu
  · simpa only [UpperCertQ.rebind_interpTerms] using hi
  · rw [UpperCertQ.rebind_objective, ho]
    exact source_objective_eq s hs
  · exact UpperCertQ.rebind_bound c hm

end LeanPEP.Adapters.ProximalGradientSource
