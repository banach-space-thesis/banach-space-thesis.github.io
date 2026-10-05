import ThesisCommon.Analysis.MeasureAlgebraL1
import ThesisCommon.Analysis.LpMeasureCoding
import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-! Constructing a Cantor coding for an arbitrary measure-algebra isomorphism
whose source sigma algebra is countably generated. The replacement sigma
algebra need not be countably generated, even pointwise. -/
noncomputable section
open Set MeasureTheory MeasurableSpace Filter
open scoped Classical

namespace ThesisCommon.MeasureAlgebraIso
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
variable (Φ : MeasureAlgebraIso μ ν)

theorem map_empty_mk : Φ.toEquiv (MeasureAlgebra.mk μ ∅ MeasurableSet.empty) =
    MeasureAlgebra.mk ν ∅ MeasurableSet.empty := by
  have h := Φ.map_iUnion Empty (fun i => nomatch i)
  simpa only [MeasureAlgebra.iUnion, iUnion_of_empty] using h

theorem map_univ_mk : Φ.toEquiv (MeasureAlgebra.mk μ univ MeasurableSet.univ) =
    MeasureAlgebra.mk ν univ MeasurableSet.univ := by
  have h := Φ.map_compl (MeasureAlgebra.mk μ ∅ MeasurableSet.empty)
  simpa only [MeasureAlgebra.compl_mk, Φ.map_empty_mk, compl_empty] using h

theorem map_preimage_generateFrom [mZ : MeasurableSpace Z]
    (C : Set (Set Z)) (hgen : generateFrom C = mZ)
    (f : X → Z) (hf : Measurable f) (g : Y → Z) (hg : Measurable g)
    (hbase : ∀ s ∈ C, ∀ hs : MeasurableSet s,
      Φ.toEquiv (MeasureAlgebra.mk μ (f ⁻¹' s) (hf hs)) =
        MeasureAlgebra.mk ν (g ⁻¹' s) (hg hs))
    (s : Set Z) (hs : MeasurableSet s) :
    Φ.toEquiv (MeasureAlgebra.mk μ (f ⁻¹' s) (hf hs)) =
      MeasureAlgebra.mk ν (g ⁻¹' s) (hg hs) := by
  subst mZ
  induction s, hs using generateFrom_induction with
  | hC s hs hm => exact hbase s hs hm
  | empty => simpa only [preimage_empty] using Φ.map_empty_mk
  | compl s hs ih =>
    simpa only [MeasureAlgebra.compl_mk, preimage_compl, ih] using
      Φ.map_compl (MeasureAlgebra.mk μ (f ⁻¹' s) (hf hs))
  | iUnion s hs ih =>
    simpa only [MeasureAlgebra.iUnion_mk, preimage_iUnion, ih] using
      Φ.map_iUnion ℕ (fun n => MeasureAlgebra.mk μ (f ⁻¹' s n) (hf (hs n)))

variable [CountablyGenerated X]

/-- The replacement-space coding records membership in representatives of the
images of the original countable generators. -/
def cantorCoding (y : Y) (n : ℕ) : Bool :=
  decide (y ∈ Φ.imageSet (natGeneratingSequence X n) (measurableSet_natGeneratingSequence (α := X) n))

theorem measurable_cantorCoding : Measurable Φ.cantorCoding := by
  rw [measurable_pi_iff]
  intro n
  apply measurable_to_bool
  simpa only [cantorCoding, preimage, mem_singleton_iff, Bool.decide_iff, setOf_mem_eq] using
    Φ.measurableSet_imageSet (natGeneratingSequence X n) (measurableSet_natGeneratingSequence (α := X) n)

theorem cantorCoding_coordinate_mk (n : ℕ) (s : Set Bool) (hs : MeasurableSet s) :
    Φ.toEquiv (MeasureAlgebra.mk μ ((mapNatBool X) ⁻¹' (Function.eval n ⁻¹' s))
      ((measurable_mapNatBool X) ((measurable_pi_apply n) hs))) =
    MeasureAlgebra.mk ν (Φ.cantorCoding ⁻¹' (Function.eval n ⁻¹' s))
      (Φ.measurable_cantorCoding ((measurable_pi_apply n) hs)) := by
  have htrue : (mapNatBool X) ⁻¹' (Function.eval n ⁻¹' ({true} : Set Bool)) =
      natGeneratingSequence X n := by ext x; simp [mapNatBool]
  have htrue' : Φ.cantorCoding ⁻¹' (Function.eval n ⁻¹' ({true} : Set Bool)) =
      Φ.imageSet (natGeneratingSequence X n) (measurableSet_natGeneratingSequence (α := X) n) := by
    ext y
    simp [cantorCoding]
  have hfalse : (mapNatBool X) ⁻¹' (Function.eval n ⁻¹' ({false} : Set Bool)) =
      (natGeneratingSequence X n)ᶜ := by ext x; simp [mapNatBool]
  have hfalse' : Φ.cantorCoding ⁻¹' (Function.eval n ⁻¹' ({false} : Set Bool)) =
      (Φ.imageSet (natGeneratingSequence X n) (measurableSet_natGeneratingSequence (α := X) n))ᶜ := by
    ext y
    simp [cantorCoding]
  by_cases ht : true ∈ s <;> by_cases hf : false ∈ s
  · have heq : s = univ := by ext b; cases b <;> simp_all
    subst s
    simpa only [preimage_univ] using Φ.map_univ_mk
  · have heq : s = {true} := by ext b; cases b <;> simp_all
    subst s
    simpa only [htrue, htrue'] using
      (Φ.mk_imageSet (natGeneratingSequence X n) (measurableSet_natGeneratingSequence (α := X) n)).symm
  · have heq : s = {false} := by ext b; cases b <;> simp_all
    subst s
    simpa only [hfalse, hfalse', MeasureAlgebra.compl_mk] using
      (Φ.map_compl (MeasureAlgebra.mk μ (natGeneratingSequence X n)
        (measurableSet_natGeneratingSequence (α := X) n))).trans
        (congrArg MeasureAlgebra.compl
          (Φ.mk_imageSet (natGeneratingSequence X n)
            (measurableSet_natGeneratingSequence (α := X) n)).symm)
  · have heq : s = ∅ := by ext b; cases b <;> simp_all
    subst s
    simpa only [preimage_empty] using Φ.map_empty_mk

/-- All Borel pullbacks, not only the generating cylinders, correspond under Φ. -/
theorem cantorCoding_preimage_mk (s : Set (ℕ → Bool)) (hs : MeasurableSet s) :
    Φ.toEquiv (MeasureAlgebra.mk μ ((mapNatBool X) ⁻¹' s) ((measurable_mapNatBool X) hs)) =
      MeasureAlgebra.mk ν (Φ.cantorCoding ⁻¹' s) (Φ.measurable_cantorCoding hs) := by
  apply Φ.map_preimage_generateFrom
    {B | ∃ (n : ℕ) (A : Set Bool), MeasurableSet A ∧ Function.eval n ⁻¹' A = B}
    MeasurableSpace.pi_eq_generateFrom_projections.symm
    (mapNatBool X) (measurable_mapNatBool X) Φ.cantorCoding Φ.measurable_cantorCoding
    ?_ s hs
  rintro _ ⟨n, A, hA, rfl⟩ _
  exact Φ.cantorCoding_coordinate_mk n A hA

theorem cantorCoding_map_measure : ν.map Φ.cantorCoding = μ.map (mapNatBool X) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply Φ.measurable_cantorCoding hs,
    Measure.map_apply (measurable_mapNatBool X) hs]
  have h := Φ.measure_eq
    (MeasureAlgebra.mk μ ((mapNatBool X) ⁻¹' s) ((measurable_mapNatBool X) hs))
  rw [Φ.cantorCoding_preimage_mk s hs] at h
  exact h

def cantorCoding_measurePreserving :
    MeasurePreserving Φ.cantorCoding ν (μ.map (mapNatBool X)) :=
  ⟨Φ.measurable_cantorCoding, Φ.cantorCoding_map_measure⟩

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The constructed coding realizes the previously constructed measure-algebra
L1 equivalence after the original Cantor pullback. -/
theorem lOneEquiv_cantor_pullback (f : Lp ℝ 1 (μ.map (mapNatBool X))) :
    Φ.lOneEquiv (lpComapEquiv μ (mapNatBool X) (measurable_mapNatBool X)
      (comap_mapNatBool X) 1 f) =
    Lp.compMeasurePreserving Φ.cantorCoding Φ.cantorCoding_measurePreserving f := by
  have hmap : Φ.lOneEquiv.toLinearIsometry.toContinuousLinearMap.comp
      (lpComapEquiv μ (mapNatBool X) (measurable_mapNatBool X)
        (comap_mapNatBool X) 1).toLinearIsometry.toContinuousLinearMap =
      (Lp.compMeasurePreservingₗᵢ ℝ Φ.cantorCoding Φ.cantorCoding_measurePreserving).toContinuousLinearMap := by
    apply lOne_continuousLinearMap_ext_indicators
    intro s hs
    have hsrc : lpComapEquiv μ (mapNatBool X) (measurable_mapNatBool X)
        (comap_mapNatBool X) 1 (lOneIndicator (μ.map (mapNatBool X)) s hs) =
        lOneIndicator μ ((mapNatBool X) ⁻¹' s) ((measurable_mapNatBool X) hs) := by
      apply Lp.ext
      filter_upwards [lpComapEquiv_coe μ (mapNatBool X) (measurable_mapNatBool X)
          (comap_mapNatBool X) 1 (lOneIndicator (μ.map (mapNatBool X)) s hs),
        ae_of_ae_map (measurable_mapNatBool X).aemeasurable
          (lOneIndicator_coe (μ := μ.map (mapNatBool X)) s hs),
        lOneIndicator_coe (μ := μ) ((mapNatBool X) ⁻¹' s) ((measurable_mapNatBool X) hs)]
        with x hx hxs hxp
      rw [hx, Function.comp_apply, hxs, hxp]
      by_cases hmem : mapNatBool X x ∈ s <;> simp [hmem]
    have htgt : Lp.compMeasurePreserving Φ.cantorCoding Φ.cantorCoding_measurePreserving
        (lOneIndicator (μ.map (mapNatBool X)) s hs) =
        lOneIndicator ν (Φ.cantorCoding ⁻¹' s) (Φ.measurable_cantorCoding hs) := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_compMeasurePreserving
          (lOneIndicator (μ.map (mapNatBool X)) s hs) Φ.cantorCoding_measurePreserving,
        Φ.cantorCoding_measurePreserving.quasiMeasurePreserving.ae
          (lOneIndicator_coe (μ := μ.map (mapNatBool X)) s hs),
        lOneIndicator_coe (μ := ν) (Φ.cantorCoding ⁻¹' s) (Φ.measurable_cantorCoding hs)]
        with y hy hys hyp
      rw [hy, Function.comp_apply, hys, hyp]
      by_cases hmem : Φ.cantorCoding y ∈ s <;> simp [hmem]
    change Φ.lOneEquiv (lpComapEquiv μ (mapNatBool X) (measurable_mapNatBool X)
      (comap_mapNatBool X) 1 (lOneIndicator (μ.map (mapNatBool X)) s hs)) = _
    rw [hsrc, Φ.lOneEquiv_indicator_of_mk_eq _ _ _ _ (Φ.cantorCoding_preimage_mk s hs)]
    exact htgt.symm
  exact DFunLike.congr_fun hmap f

theorem lOneEquiv_cantor_pullback_coe (f : Lp ℝ 1 (μ.map (mapNatBool X))) :
    Φ.lOneEquiv (lpComapEquiv μ (mapNatBool X) (measurable_mapNatBool X)
      (comap_mapNatBool X) 1 f) =ᵐ[ν] f ∘ Φ.cantorCoding := by
  rw [Φ.lOneEquiv_cantor_pullback]
  exact Lp.coeFn_compMeasurePreserving f Φ.cantorCoding_measurePreserving

end ThesisCommon.MeasureAlgebraIso
