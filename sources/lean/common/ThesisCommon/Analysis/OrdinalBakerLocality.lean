import ThesisCommon.Analysis.OrdinalDerived

/-! Derived sets are local on clopen sets. Every ordinal initial closed
interval is also open, allowing the global arithmetic calculation to be
restricted to compact ordinal intervals. -/
noncomputable section
open Set Order Filter Topology
universe u v
namespace ThesisCommon
variable {K : Type v} [TopologicalSpace K]

theorem derivedSet_inter_clopen (A : Set K) {U : Set K} (hU : IsClopen U) :
    derivedSet (A ∩ U) = derivedSet A ∩ U := by
  apply Subset.antisymm
  · intro x hx
    exact ⟨derivedSet_mono _ _ inter_subset_left hx,
      hU.isClosed.closure_subset ((closure_mono inter_subset_right)
        (derivedSet_subset_closure _ hx))⟩
  · rintro x ⟨hx, hxU⟩
    rw [mem_derivedSet, accPt_iff_nhds]
    intro V hV
    obtain ⟨y, ⟨⟨hyV, hyU⟩, hyA⟩, hxy⟩ :=
      (accPt_iff_nhds.mp hx) (V ∩ U) (inter_mem hV (hU.isOpen.mem_nhds hxU))
    exact ⟨y, ⟨hyV, hyA, hyU⟩, hxy⟩

theorem ordinalDerived_inter_clopen (A : Set K) {U : Set K} (hU : IsClopen U)
    (α : Ordinal.{u}) : ordinalDerived (A ∩ U) α = ordinalDerived A α ∩ U := by
  induction α using Ordinal.limitRecOn with
  | zero => simp
  | succ α ih => rw [ordinalDerived_succ, ordinalDerived_succ, ih, derivedSet_inter_clopen _ hU]
  | limit α hα ih =>
      rw [ordinalDerived_limit _ hα, ordinalDerived_limit _ hα]
      ext x
      constructor
      · intro hx
        have hx0 := mem_iInter₂.mp hx 0 hα.bot_lt
        rw [ih 0 hα.bot_lt] at hx0
        refine ⟨mem_iInter₂.mpr (fun β hβ => ?_), hx0.2⟩
        have hxβ := mem_iInter₂.mp hx β hβ
        rw [ih β hβ] at hxβ
        exact hxβ.1
      · rintro ⟨hx, hxU⟩
        apply mem_iInter₂.mpr
        intro β hβ
        rw [ih β hβ]
        exact ⟨mem_iInter₂.mp hx β hβ, hxU⟩

theorem ordinal_isClopen_Iic (β : Ordinal.{u}) : IsClopen (Iic β) := by
  refine ⟨isClosed_Iic, ?_⟩
  rw [← Iio_succ]
  exact isOpen_Iio

theorem ordinalDerived_Iic (β α : Ordinal.{u}) :
    ordinalDerived (Iic β) α = ordinalDerived (univ : Set Ordinal.{u}) α ∩ Iic β := by
  simpa only [univ_inter] using ordinalDerived_inter_clopen univ (ordinal_isClopen_Iic β) α

end ThesisCommon
