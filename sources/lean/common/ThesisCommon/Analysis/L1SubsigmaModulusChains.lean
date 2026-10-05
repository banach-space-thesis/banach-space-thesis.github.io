import ThesisCommon.Analysis.L1SubsigmaProjection
import ThesisCommon.Analysis.L1SubsigmaChains
import ThesisCommon.Analysis.L1OperatorLattice
import ThesisCommon.Analysis.LatticeIntervalDensity

/-! Equalities between restricted operator moduli pass to the closure of
an increasing chain of actual L1 sublattices. The proof clips approximating
inputs to the required order interval. This supplies the singularity part
of the chain-closure argument in PEMS Lemma 4.9. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} {m₀ : MeasurableSpace X} {n₀ : MeasurableSpace Y}
variable {μ : @Measure X m₀} {ν : @Measure Y n₀} [IsFiniteMeasure μ]

def lOneSubsigmaModulusExtension (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    {m : MeasurableSpace X} (hm : m ≤ m₀) : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  |T.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap|.comp
    (lOneSubsigmaRetraction μ hm)

theorem lOneSubsigmaModulusExtension_embedding
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) {m : MeasurableSpace X} (hm : m ≤ m₀)
    (f : Lp ℝ 1 (μ.trim hm)) :
    lOneSubsigmaModulusExtension T hm (lOneSubsigmaEmbedding μ hm f) =
      |T.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap| f := by
  have h := DFunLike.congr_fun (lOneSubsigmaRetraction_embedding μ hm) f
  change lOneSubsigmaRetraction μ hm (lOneSubsigmaEmbedding μ hm f) = f at h
  simp only [lOneSubsigmaModulusExtension, ContinuousLinearMap.comp_apply, h]

theorem lOneSubsigmaModulusExtension_isLUB
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) {m : MeasurableSpace X} (hm : m ≤ m₀)
    {f : Lp ℝ 1 μ} (hf : 0 ≤ f) (hfm : f ∈ lOneSubsigma μ m) :
    IsLUB (T '' (Icc (-f) f ∩ (lOneSubsigma μ m : Set (Lp ℝ 1 μ))))
      (lOneSubsigmaModulusExtension T hm f) := by
  change f ∈ (lOneSubsigma μ m : Set (Lp ℝ 1 μ)) at hfm
  rw [← range_lOneSubsigmaEmbedding μ hm] at hfm
  obtain ⟨u, rfl⟩ := hfm
  have hu : 0 ≤ u := (lOneSubsigmaEmbedding_le_iff μ hm 0 u).mp (by simpa using hf)
  have heq : (lOneSubsigmaEmbedding μ hm) '' Icc (-u) u =
      Icc (-lOneSubsigmaEmbedding μ hm u) (lOneSubsigmaEmbedding μ hm u) ∩
        (lOneSubsigma μ m : Set (Lp ℝ 1 μ)) := by
    ext g
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨?_, (lOneSubsigmaEmbedding_le_iff μ hm v u).mpr hv.2⟩, ?_⟩
      · simpa only [map_neg] using (lOneSubsigmaEmbedding_le_iff μ hm (-u) v).mpr hv.1
      · rw [← range_lOneSubsigmaEmbedding μ hm]
        exact mem_range_self v
    · rintro ⟨hg, hgm⟩
      rw [← range_lOneSubsigmaEmbedding μ hm] at hgm
      obtain ⟨v, rfl⟩ := hgm
      refine ⟨v, ⟨?_, (lOneSubsigmaEmbedding_le_iff μ hm v u).mp hg.2⟩, rfl⟩
      apply (lOneSubsigmaEmbedding_le_iff μ hm (-u) v).mp
      simpa only [map_neg] using hg.1
  rw [← heq, image_image, lOneSubsigmaModulusExtension_embedding, abs_lOneOperator_eq]
  exact @lOneOperatorModulus_rieszKantorovich X Y m n₀ (μ.trim hm) ν
    (T.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) u hu

theorem lOneSubsigma_moduli_eq_iSup
    (A B : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (m : ℕ → MeasurableSpace X)
    (hm : ∀ n, m n ≤ m₀) (hmono : Monotone (fun n => lOneSubsigma μ (m n)))
    (hmod : ∀ n,
      |A.comp (lOneSubsigmaEmbedding μ (hm n)).toContinuousLinearMap| =
      |B.comp (lOneSubsigmaEmbedding μ (hm n)).toContinuousLinearMap|) :
    |A.comp (lOneSubsigmaEmbedding μ (iSup_le hm)).toContinuousLinearMap| =
      |B.comp (lOneSubsigmaEmbedding μ (iSup_le hm)).toContinuousLinearMap| := by
  let P : Submodule ℝ (Lp ℝ 1 μ) := ⨆ n, lOneSubsigma μ (m n)
  let mf := ⨆ n, m n
  have hPcoe : (P : Set (Lp ℝ 1 μ)) = ⋃ n, (lOneSubsigma μ (m n) : Set (Lp ℝ 1 μ)) :=
    Submodule.coe_iSup_of_directed _ hmono.directed_le
  have hPclosure : closure (P : Set (Lp ℝ 1 μ)) =
      (lOneSubsigma μ mf : Set (Lp ℝ 1 μ)) := by
    have h := congrArg (fun Q : Submodule ℝ (Lp ℝ 1 μ) => (Q : Set (Lp ℝ 1 μ)))
      (richChainClosure_lOneSubsigma μ m hm hmono)
    simpa only [richChainClosure, Submodule.topologicalClosure_coe] using h
  have hPinf : ∀ f ∈ P, ∀ g ∈ P, f ⊓ g ∈ P := by
    intro f hf g hg
    change f ∈ (P : Set (Lp ℝ 1 μ)) at hf
    change g ∈ (P : Set (Lp ℝ 1 μ)) at hg
    change f ⊓ g ∈ (P : Set (Lp ℝ 1 μ))
    rw [hPcoe] at hf hg ⊢
    obtain ⟨i, hi⟩ := mem_iUnion.mp hf
    obtain ⟨j, hj⟩ := mem_iUnion.mp hg
    exact mem_iUnion.mpr ⟨max i j, lOneSubsigma_inf_mem μ
      (hmono (le_max_left i j) hi) (hmono (le_max_right i j) hj)⟩
  have hPsup : ∀ f ∈ P, ∀ g ∈ P, f ⊔ g ∈ P := by
    intro f hf g hg
    change f ∈ (P : Set (Lp ℝ 1 μ)) at hf
    change g ∈ (P : Set (Lp ℝ 1 μ)) at hg
    change f ⊔ g ∈ (P : Set (Lp ℝ 1 μ))
    rw [hPcoe] at hf hg ⊢
    obtain ⟨i, hi⟩ := mem_iUnion.mp hf
    obtain ⟨j, hj⟩ := mem_iUnion.mp hg
    exact mem_iUnion.mpr ⟨max i j, lOneSubsigma_sup_mem μ
      (hmono (le_max_left i j) hi) (hmono (le_max_right i j) hj)⟩
  have hPf : P ≤ lOneSubsigma μ mf := iSup_le fun n =>
    lOneSubsigma_mono μ (le_iSup m n)
  have hle (A B : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
      (hmod : ∀ n, |A.comp (lOneSubsigmaEmbedding μ (hm n)).toContinuousLinearMap| =
        |B.comp (lOneSubsigmaEmbedding μ (hm n)).toContinuousLinearMap|)
      (f : Lp ℝ 1 μ) (hf : 0 ≤ f) (hfP : f ∈ P) :
      lOneSubsigmaModulusExtension A (iSup_le hm) f ≤
        lOneSubsigmaModulusExtension B (iSup_le hm) f := by
    apply (lOneSubsigmaModulusExtension_isLUB A (iSup_le hm) hf (hPf hfP)).2
    rintro _ ⟨g, hg, rfl⟩
    apply continuousLinearMap_interval_bound_of_dense_sublattice A P hPinf hPsup hf hfP
      hg.1 (by rw [hPclosure]; exact hg.2)
    intro u hu
    have hfP' : f ∈ (P : Set (Lp ℝ 1 μ)) := hfP
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hPcoe ▸ hfP')
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hPcoe ▸ hu.2)
    have hfij := hmono (le_max_left i j) hi
    have huij := hmono (le_max_right i j) hj
    have hlocal := (lOneSubsigmaModulusExtension_isLUB A (hm (max i j)) hf hfij).1
      (show A u ∈ A '' (Icc (-f) f ∩ (lOneSubsigma μ (m (max i j)) : Set (Lp ℝ 1 μ)))
        from ⟨u, ⟨hu.1, huij⟩, rfl⟩)
    have hext : lOneSubsigmaModulusExtension A (hm (max i j)) =
        lOneSubsigmaModulusExtension B (hm (max i j)) := by
      unfold lOneSubsigmaModulusExtension
      rw [hmod]
    rw [hext] at hlocal
    apply hlocal.trans
    apply (lOneSubsigmaModulusExtension_isLUB B (hm (max i j)) hf hfij).2
    rintro _ ⟨v, hv, rfl⟩
    exact (lOneSubsigmaModulusExtension_isLUB B (iSup_le hm) hf (hPf hfP)).1
      ⟨v, ⟨hv.1, lOneSubsigma_mono μ (le_iSup m (max i j)) hv.2⟩, rfl⟩
  have hpos (f : Lp ℝ 1 μ) (hf : 0 ≤ f) (hfP : f ∈ P) :
      lOneSubsigmaModulusExtension A (iSup_le hm) f =
        lOneSubsigmaModulusExtension B (iSup_le hm) f :=
    le_antisymm (hle A B hmod f hf hfP) (hle B A (fun n => (hmod n).symm) f hf hfP)
  have heqP : EqOn (lOneSubsigmaModulusExtension A (iSup_le hm))
      (lOneSubsigmaModulusExtension B (iSup_le hm)) (P : Set (Lp ℝ 1 μ)) := by
    intro f hf
    have hfp : f⁺ ∈ P := hPsup f hf 0 P.zero_mem
    have hfn : f⁻ ∈ P := hPsup (-f) (P.neg_mem hf) 0 P.zero_mem
    conv_lhs => rw [← posPart_sub_negPart f, map_sub]
    conv_rhs => rw [← posPart_sub_negPart f, map_sub]
    rw [hpos _ (posPart_nonneg f) hfp, hpos _ (negPart_nonneg f) hfn]
  have heqf := heqP.closure (lOneSubsigmaModulusExtension A (iSup_le hm)).continuous
    (lOneSubsigmaModulusExtension B (iSup_le hm)).continuous
  rw [hPclosure] at heqf
  apply ContinuousLinearMap.ext
  intro f
  have hf : lOneSubsigmaEmbedding μ (iSup_le hm) f ∈ lOneSubsigma μ mf := by
    change lOneSubsigmaEmbedding μ (iSup_le hm) f ∈
      (lOneSubsigma μ (⨆ n, m n) : Set (Lp ℝ 1 μ))
    rw [← range_lOneSubsigmaEmbedding μ (iSup_le hm)]
    exact mem_range_self f
  have h := heqf hf
  simpa only [lOneSubsigmaModulusExtension_embedding] using h

end ThesisCommon
