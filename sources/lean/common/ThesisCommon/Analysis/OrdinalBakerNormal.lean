import ThesisCommon.Analysis.OrdinalBakerDerived

/-! Normal ordinal maps are closed topological embeddings. In particular
ordinal multiplication transfers derived-set calculations through its actual
continuous embedding. -/
noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

theorem ordinal_normal_isClosedMap {f : Ordinal.{u} → Ordinal.{u}}
    (hf : IsNormal f) : IsClosedMap f := by
  intro A hA
  apply Ordinal.isClosed_iff_iSup.mpr
  intro ι hι g hg
  letI := hι
  choose a ha heq using hg
  refine ⟨⨆ i, a i, Ordinal.isClosed_iff_iSup.mp hA hι a ha, ?_⟩
  rw [hf.map_iSup]
  · simp only [heq]
  · exact Ordinal.bddAbove_range a

theorem ordinal_normal_isClosedEmbedding {f : Ordinal.{u} → Ordinal.{u}}
    (hf : IsNormal f) : IsClosedEmbedding f :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap hf.continuous hf.strictMono.injective
    (ordinal_normal_isClosedMap hf)

theorem ordinal_mem_derivedSet_univ_iff {a : Ordinal.{u}} :
    a ∈ derivedSet (univ : Set Ordinal.{u}) ↔ IsSuccLimit a := by
  constructor
  · exact fun h => Ordinal.IsAcc.isSuccLimit h
  · intro h
    apply (Ordinal.isAcc_iff a univ).mpr
    refine ⟨h.ne_bot, ?_⟩
    intro b hb
    exact ⟨succ b, mem_univ _, lt_succ b, h.succ_lt hb⟩

theorem ordinal_derivedSet_univ : derivedSet (univ : Set Ordinal.{u}) =
    {a | a ≠ 0 ∧ Ordinal.omega0 ∣ a} := by
  ext a
  rw [ordinal_mem_derivedSet_univ_iff, Ordinal.isSuccLimit_iff_omega0_dvd]
  rfl

end ThesisCommon
