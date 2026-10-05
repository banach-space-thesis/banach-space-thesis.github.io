import ThesisCommon.Analysis.MeasureAlgebraMap
import ThesisCommon.Analysis.L1IndicatorExt

/-! Representatives and real L1 indicators associated to an arbitrary
measure-algebra isomorphism. No point map between the measure spaces is used. -/
noncomputable section
open Set MeasureTheory Filter

namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

namespace MeasureAlgebra

theorem iUnion_bool_mk (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    iUnion (fun b : Bool => if b then mk μ s hs else mk μ t ht) =
      mk μ (s ∪ t) (hs.union ht) := by
  have h : (fun b : Bool => if b then mk μ s hs else mk μ t ht) =
      fun b : Bool => mk μ (if b then s else t) (by cases b <;> simp_all) := by
    funext b
    cases b <;> rfl
  rw [h, iUnion_mk]
  congr 1
  ext x
  simp [or_comm]

theorem iInter_bool_mk (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    iInter (fun b : Bool => if b then mk μ s hs else mk μ t ht) =
      mk μ (s ∩ t) (hs.inter ht) := by
  have h : (fun b : Bool => if b then mk μ s hs else mk μ t ht) =
      fun b : Bool => mk μ (if b then s else t) (by cases b <;> simp_all) := by
    funext b
    cases b <;> rfl
  rw [h, iInter_mk]
  congr 1
  ext x
  simp [and_comm]

end MeasureAlgebra

namespace MeasureAlgebraIso
variable (Φ : MeasureAlgebraIso μ ν)

def imageSet (s : Set X) (hs : MeasurableSet s) : Set Y :=
  (Φ.toEquiv (MeasureAlgebra.mk μ s hs)).representative.val

theorem measurableSet_imageSet (s : Set X) (hs : MeasurableSet s) :
    MeasurableSet (Φ.imageSet s hs) :=
  (Φ.toEquiv (MeasureAlgebra.mk μ s hs)).representative.property

theorem mk_imageSet (s : Set X) (hs : MeasurableSet s) :
    MeasureAlgebra.mk ν (Φ.imageSet s hs) (Φ.measurableSet_imageSet s hs) =
      Φ.toEquiv (MeasureAlgebra.mk μ s hs) :=
  MeasureAlgebra.mk_representative _

theorem measure_imageSet (s : Set X) (hs : MeasurableSet s) :
    ν (Φ.imageSet s hs) = μ s := by
  have h := Φ.measure_eq (MeasureAlgebra.mk μ s hs)
  rw [← Φ.mk_imageSet s hs] at h
  exact h

theorem imageSet_union_ae (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    Φ.imageSet (s ∪ t) (hs.union ht) =ᵐ[ν] (Φ.imageSet s hs ∪ Φ.imageSet t ht : Set Y) := by
  apply (MeasureAlgebra.mk_eq_mk (Φ.measurableSet_imageSet _ _)
    ((Φ.measurableSet_imageSet s hs).union (Φ.measurableSet_imageSet t ht))).mp
  rw [Φ.mk_imageSet, ← MeasureAlgebra.iUnion_bool_mk s t hs ht,
    ← MeasureAlgebra.iUnion_bool_mk _ _ (Φ.measurableSet_imageSet s hs)
      (Φ.measurableSet_imageSet t ht)]
  simp_rw [Φ.mk_imageSet]
  have h := Φ.map_iUnion Bool (fun b => if b then MeasureAlgebra.mk μ s hs
    else MeasureAlgebra.mk μ t ht)
  simpa only [apply_ite] using h

theorem imageSet_inter_ae (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    Φ.imageSet (s ∩ t) (hs.inter ht) =ᵐ[ν] (Φ.imageSet s hs ∩ Φ.imageSet t ht : Set Y) := by
  apply (MeasureAlgebra.mk_eq_mk (Φ.measurableSet_imageSet _ _)
    ((Φ.measurableSet_imageSet s hs).inter (Φ.measurableSet_imageSet t ht))).mp
  rw [Φ.mk_imageSet, ← MeasureAlgebra.iInter_bool_mk s t hs ht,
    ← MeasureAlgebra.iInter_bool_mk _ _ (Φ.measurableSet_imageSet s hs)
      (Φ.measurableSet_imageSet t ht)]
  simp_rw [Φ.mk_imageSet]
  have h := Φ.map_iInter (fun b : Bool => if b then MeasureAlgebra.mk μ s hs
    else MeasureAlgebra.mk μ t ht)
  simpa only [apply_ite] using h

theorem imageSet_inter_null_of_disjoint (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    ν (Φ.imageSet s hs ∩ Φ.imageSet t ht) = 0 := by
  rw [← measure_congr (Φ.imageSet_inter_ae s t hs ht), Φ.measure_imageSet,
    Set.disjoint_iff_inter_eq_empty.mp hst, measure_empty]

theorem symm_imageSet_imageSet_ae (s : Set X) (hs : MeasurableSet s) :
    Φ.symm.imageSet (Φ.imageSet s hs) (Φ.measurableSet_imageSet s hs) =ᵐ[μ] s := by
  apply (MeasureAlgebra.mk_eq_mk _ hs).mp
  rw [Φ.symm.mk_imageSet, Φ.mk_imageSet]
  exact Φ.toEquiv.symm_apply_apply _

end MeasureAlgebraIso

variable [IsFiniteMeasure μ]

theorem lOneIndicator_eq_of_ae {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s =ᵐ[μ] t) : lOneIndicator μ s hs = lOneIndicator μ t ht := by
  apply Lp.ext
  filter_upwards [lOneIndicator_coe (μ := μ) s hs, lOneIndicator_coe (μ := μ) t ht, hst]
    with x hxs hxt hx
  rw [hxs, hxt]
  change (x ∈ s) = (x ∈ t) at hx
  by_cases hxs' : x ∈ s <;> by_cases hxt' : x ∈ t <;> simp_all

theorem norm_lOneIndicator (s : Set X) (hs : MeasurableSet s) :
    ‖lOneIndicator μ s hs‖ = μ.real s := by
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ x, ‖lOneIndicator μ s hs x‖ ∂μ) = ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [lOneIndicator_coe (μ := μ) s hs] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    _ = μ.real s := by rw [integral_indicator hs]; simp

theorem lOneIndicator_union_of_inter_null (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : μ (s ∩ t) = 0) :
    lOneIndicator μ (s ∪ t) (hs.union ht) = lOneIndicator μ s hs + lOneIndicator μ t ht := by
  apply Lp.ext
  filter_upwards [lOneIndicator_coe (μ := μ) (s ∪ t) (hs.union ht),
    lOneIndicator_coe (μ := μ) s hs, lOneIndicator_coe (μ := μ) t ht,
    Lp.coeFn_add (lOneIndicator μ s hs) (lOneIndicator μ t ht),
    measure_eq_zero_iff_ae_notMem.mp hst] with x hu hsx htx hadd hx
  simp only [Pi.add_apply] at hadd
  rw [hu, hadd, hsx, htx]
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp_all

end ThesisCommon
