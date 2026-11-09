import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Separation.Regular

/-! A genuine locally trivial bundle core with compact fiber over a compact
regular base has compact total space. The proof uses finite closed chart
neighborhoods, not an assumed compactness or properness of the projection. -/

noncomputable section

namespace BanachIsometric

open Set Bundle
open scoped Topology

variable {ι B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    (Z : FiberBundleCore ι B F)

theorem isCompact_bundleCore_chart_preimage [CompactSpace F] (i : ι) {K : Set B}
    (hK : IsCompact K) (hKi : K ⊆ Z.baseSet i) : IsCompact (Z.proj ⁻¹' K) := by
  let e := Z.localTriv i
  have hsub : K ×ˢ (univ : Set F) ⊆ e.target := by
    rintro ⟨a, v⟩ ha
    exact e.mem_target.mpr (hKi ha.1)
  have hc : IsCompact (e.toPartialEquiv.symm '' (K ×ˢ (univ : Set F))) :=
    (hK.prod isCompact_univ).image_of_continuousOn (e.continuousOn_invFun.mono hsub)
  have heq : e.toPartialEquiv.symm '' (K ×ˢ (univ : Set F)) = Z.proj ⁻¹' K := by
    ext t
    constructor
    · rintro ⟨⟨a, v⟩, ha, rfl⟩
      change Z.proj (e.toPartialEquiv.symm (a, v)) ∈ K
      have hp := e.proj_symm_apply (hsub ha)
      change Z.proj (e.toPartialEquiv.symm (a, v)) = a at hp
      rw [hp]
      exact ha.1
    · intro ht
      refine ⟨(Z.proj t, (e t).2), ⟨ht, mem_univ _⟩, ?_⟩
      exact e.symm_apply_mk_proj (e.mem_source.mpr (hKi ht))
  rwa [heq] at hc

theorem compactSpace_bundleCore_totalSpace [RegularSpace B] [CompactSpace B] [CompactSpace F] :
    CompactSpace Z.TotalSpace := by
  classical
  choose K hKn hKc hKs using fun b : B => exists_mem_nhds_isClosed_subset
    ((Z.isOpen_baseSet (Z.indexAt b)).mem_nhds (Z.mem_baseSet_at b))
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover (fun b => interior (K b))
    (fun _ => isOpen_interior) (by
      intro b _
      exact mem_iUnion.mpr ⟨b, mem_interior_iff_mem_nhds.mpr (hKn b)⟩)
  have hC : IsCompact (⋃ b ∈ I, Z.proj ⁻¹' K b) :=
    I.isCompact_biUnion (fun b _ =>
      isCompact_bundleCore_chart_preimage Z (Z.indexAt b) (hKc b).isCompact (hKs b))
  have hcover : (⋃ b ∈ I, Z.proj ⁻¹' K b) = univ := by
    apply eq_univ_of_forall
    intro t
    obtain ⟨b, hb, hbt⟩ := mem_iUnion₂.mp (hI (mem_univ (Z.proj t)))
    exact mem_iUnion₂.mpr ⟨b, hb, (interior_subset : interior (K b) ⊆ K b) hbt⟩
  exact ⟨hcover ▸ hC⟩

end BanachIsometric
