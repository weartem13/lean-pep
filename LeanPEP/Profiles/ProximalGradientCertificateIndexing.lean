import LeanPEP.Profiles.ProximalGradientCertificate
import LeanPEP.Profiles.CompositeConstraintIndexing

/-! # Actual constraint lookups for the unchanged C3A certificate -/

namespace LeanPEP.Profiles.ProximalGradientCertificate

open LeanPEP.GramPEP
open LeanPEP.Profiles.ProximalGradient
open LeanPEP.Profiles.Composite (rowMajorList)

private def smoothRows (n : ℕ) := rowMajorList (n + 3) (n + 3) fun i j =>
  Composite.interpolationExprQ .oneSmoothConvex (smoothSamplesQ n i) (smoothSamplesQ n j)
private def nonsmoothRows (n : ℕ) := rowMajorList (n + 2) (n + 2) fun i j =>
  Composite.interpolationExprQ .convex (nonsmoothSamplesQ n i) (nonsmoothSamplesQ n j)

private theorem constraint_blocks (n : ℕ) :
    (modelQ n).assumptions = smoothRows n ++ nonsmoothRows n ++ [radiusExprQ n] :=
  modelQ_constraints n

private theorem smoothRows_length (n : ℕ) : (smoothRows n).length = (n + 3) ^ 2 := by
  simp [smoothRows, pow_two]
private theorem nonsmoothRows_length (n : ℕ) : (nonsmoothRows n).length = (n + 2) ^ 2 := by
  simp [nonsmoothRows, pow_two]

/-- Smooth row-major indices retrieve the original component's ordered slack. -/
theorem smoothIndex_get (n : ℕ) (i j : Fin (n + 3)) :
    (modelQ n).assumptions.get (smoothIndex n i j) =
      Composite.interpolationExprQ .oneSmoothConvex (smoothSamplesQ n i) (smoothSamplesQ n j) := by
  have hij : i.val * (n + 3) + j.val < (smoothRows n).length := by
    rw [smoothRows_length]
    have hm := Nat.mul_le_mul_right (n + 3) (Nat.succ_le_of_lt i.isLt)
    have hj := j.isLt
    nlinarith
  have he : (modelQ n).assumptions[i.val * (n + 3) + j.val]? =
      some (Composite.interpolationExprQ .oneSmoothConvex
        (smoothSamplesQ n i) (smoothSamplesQ n j)) := by
    rw [constraint_blocks, List.append_assoc, List.getElem?_append_left hij]
    exact Composite.rowMajorList_getElem? _ _ _ i j
  have hbound : i.val * (n + 3) + j.val < (modelQ n).assumptions.length :=
    (smoothIndex n i j).isLt
  rw [List.getElem?_eq_getElem hbound] at he
  exact Option.some.inj he

/-- The nonsmooth offset skips the entire smooth block, not just its active rows. -/
theorem nonsmoothIndex_get (n : ℕ) (i j : Fin (n + 2)) :
    (modelQ n).assumptions.get (nonsmoothIndex n i j) =
      Composite.interpolationExprQ .convex (nonsmoothSamplesQ n i) (nonsmoothSamplesQ n j) := by
  have hij : i.val * (n + 2) + j.val < (nonsmoothRows n).length := by
    rw [nonsmoothRows_length]
    have hm := Nat.mul_le_mul_right (n + 2) (Nat.succ_le_of_lt i.isLt)
    have hj := j.isLt
    nlinarith
  have hge : (smoothRows n).length ≤ (n + 3) ^ 2 + i.val * (n + 2) + j.val := by
    rw [smoothRows_length]
    omega
  have he : (modelQ n).assumptions[(n + 3) ^ 2 + i.val * (n + 2) + j.val]? =
      some (Composite.interpolationExprQ .convex
        (nonsmoothSamplesQ n i) (nonsmoothSamplesQ n j)) := by
    rw [constraint_blocks, List.append_assoc, List.getElem?_append_right hge, smoothRows_length]
    rw [show (n + 3) ^ 2 + i.val * (n + 2) + j.val - (n + 3) ^ 2 =
        i.val * (n + 2) + j.val by omega]
    rw [List.getElem?_append_left hij]
    exact Composite.rowMajorList_getElem? _ _ _ i j
  have hbound : (n + 3) ^ 2 + i.val * (n + 2) + j.val < (modelQ n).assumptions.length :=
    (nonsmoothIndex n i j).isLt
  rw [List.getElem?_eq_getElem hbound] at he
  exact Option.some.inj he

/-- Radius is the last constraint, including at the one-step boundary n=0. -/
theorem radiusIndex_get (n : ℕ) :
    (modelQ n).assumptions.get (radiusIndex n) = radiusExprQ n := by
  have hge : (smoothRows n).length ≤ (n + 3) ^ 2 + (n + 2) ^ 2 := by
    rw [smoothRows_length]
    omega
  have he : (modelQ n).assumptions[(n + 3) ^ 2 + (n + 2) ^ 2]? = some (radiusExprQ n) := by
    rw [constraint_blocks, List.append_assoc, List.getElem?_append_right hge, smoothRows_length]
    rw [Nat.add_sub_cancel_left]
    have htail : (nonsmoothRows n).length ≤ (n + 2) ^ 2 := by
      rw [nonsmoothRows_length]
    rw [List.getElem?_append_right htail]
    simp [nonsmoothRows_length]
  have hbound : (n + 3) ^ 2 + (n + 2) ^ 2 < (modelQ n).assumptions.length :=
    (radiusIndex n).isLt
  rw [List.getElem?_eq_getElem hbound] at he
  exact Option.some.inj he

end LeanPEP.Profiles.ProximalGradientCertificate
