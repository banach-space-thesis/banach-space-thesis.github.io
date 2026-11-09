import BanachIsometric.NonvanishingConeSignedIndexHomotopy
import BanachIsometric.ConeGeometry
import BanachIsometric.RadialEvaluationHomotopy
import BanachIsometric.LipschitzOrthogonalHomotopy

/-!
# The actual evaluated exact-family cone has the normal map's signed index

Positive parallel interpolation joins the evaluated map to its normalization.
The actual orthogonal sphere homotopy joins that normalization to the normal
field. Both homotopies have proved Lipschitz slices, so the canonical signed
index comparison follows from the analytic homotopy theorem.
-/

namespace BanachIsometric.ExactTangentialFamily

open MeasureTheory Set Metric
open scoped Topology NNReal

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {g : V → ℝ} {p : E → ℝ} (A : ExactTangentialFamily E V g p)
  {n : ℕ} [NeZero n]

theorem coneEvaluation_localSignedIndex_eq_direction
    (e : V ≃L[ℝ] PiolaSpace n) (hg0 : g 0 = 0) {y : E} (hy : 0 < p y)
    (a b : PiolaSpace n) (hab : a ≤ b) (hzero : (0 : PiolaSpace n) ∈ interior (Icc a b)) :
    localSignedIndex (coordinateMapConjugate e (A.coneEvaluation y)) a b 0 =
      localSignedIndex (coordinateMapConjugate e
        (coneExtension (fun z => ((A.direction hg0 hy) z).val))) a b 0 := by
  let H : unitInterval → sphere (0 : V) 1 → V :=
    fun t z => A.radialDirectionHomotopy hg0 hy (t, z)
  have hH : Continuous (fun z : unitInterval × sphere (0 : V) 1 => H z.1 z.2) :=
    (A.radialDirectionHomotopy hg0 hy).continuous
  have hindex := localSignedIndex_coordinate_nonvanishing_cone_homotopy_of_zero_mem_interior
    e H hH (A.radialDirectionHomotopy_slices_lipschitz hg0 hy)
    (A.radialDirectionHomotopy_ne_zero hg0 hy) a b hab hzero (0 : unitInterval) 1
  have h0 : H 0 = (fun z => A.maps z y) := by
    funext z
    exact (A.radialDirectionHomotopy hg0 hy).apply_zero z
  have h1 : H 1 = (fun z => ((A.direction hg0 hy) z).val) := by
    funext z
    exact (A.radialDirectionHomotopy hg0 hy).apply_one z
  rw [h0, h1] at hindex
  simpa only [A.coneEvaluation_eq y] using hindex

theorem direction_localSignedIndex_eq_normal
    (e : V ≃L[ℝ] PiolaSpace n) (hg0 : g 0 = 0) {y : E} (hy : 0 < p y)
    (hnormal : ∃ L : ℝ≥0, LipschitzWith L A.normal)
    (a b : PiolaSpace n) (hab : a ≤ b) (hzero : (0 : PiolaSpace n) ∈ interior (Icc a b)) :
    localSignedIndex (coordinateMapConjugate e
        (coneExtension (fun z => ((A.direction hg0 hy) z).val))) a b 0 =
      localSignedIndex (coordinateMapConjugate e (coneExtension (fun z => (A.normal z).val))) a b 0 := by
  obtain ⟨Cn, hCn⟩ := hnormal
  obtain ⟨Cd, hCd⟩ := A.exists_lipschitz_direction hg0 hy
  let H : unitInterval → sphere (0 : V) 1 → sphere (0 : V) 1 :=
    fun t z => A.normalDirectionHomotopy hg0 hy (t, z)
  have hH : Continuous (fun z : unitInterval × sphere (0 : V) 1 => H z.1 z.2) :=
    (A.normalDirectionHomotopy hg0 hy).continuous
  have hLip : ∀ t, ∃ L : ℝ≥0, LipschitzWith L (H t) :=
    exists_lipschitz_orthogonalSphereHomotopy_slices A.normal (A.direction hg0 hy)
      (A.normal_inner_direction hg0 hy) hCn hCd
  have hindex := localSignedIndex_coordinate_cone_homotopy_of_zero_mem_interior
    e H hH hLip a b hab hzero (0 : unitInterval) 1
  have h0 : H 0 = A.normal := by
    funext z
    exact (A.normalDirectionHomotopy hg0 hy).apply_zero z
  have h1 : H 1 = A.direction hg0 hy := by
    funext z
    exact (A.normalDirectionHomotopy hg0 hy).apply_one z
  rw [h0, h1] at hindex
  exact hindex.symm

theorem coneEvaluation_localSignedIndex_eq_normal
    (e : V ≃L[ℝ] PiolaSpace n) (hg0 : g 0 = 0) {y : E} (hy : 0 < p y)
    (hnormal : ∃ L : ℝ≥0, LipschitzWith L A.normal)
    (a b : PiolaSpace n) (hab : a ≤ b) (hzero : (0 : PiolaSpace n) ∈ interior (Icc a b)) :
    localSignedIndex (coordinateMapConjugate e (A.coneEvaluation y)) a b 0 =
      localSignedIndex (coordinateMapConjugate e (coneExtension (fun z => (A.normal z).val))) a b 0 := by
  exact (A.coneEvaluation_localSignedIndex_eq_direction e hg0 hy a b hab hzero).trans
    (A.direction_localSignedIndex_eq_normal e hg0 hy hnormal a b hab hzero)

end BanachIsometric.ExactTangentialFamily
