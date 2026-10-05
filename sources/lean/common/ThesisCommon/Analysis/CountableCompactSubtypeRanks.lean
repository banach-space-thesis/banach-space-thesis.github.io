import ThesisCommon.Analysis.CountableCompactRankBound
import ThesisCommon.Analysis.OrdinalBakerDerived
import Mathlib.Data.Set.Card

/-! Transport of the actual transfinite derivative from a closed subset
to its subspace topology, including finiteness, nonemptiness and cardinality. -/
noncomputable section
open Set Topology Order
universe u
namespace ThesisCommon
variable {K : Type u} [MetricSpace K]

theorem ordinalDerived_subtype_image (A : Set K) (hA : IsClosed A) (α : Ordinal.{u}) :
    (Subtype.val : A → K) '' ordinalDerived (univ : Set A) α = ordinalDerived A α := by
  simpa only [image_univ, Subtype.range_coe] using
    (ordinalDerived_image_closedEmbedding hA.isClosedEmbedding_subtypeVal univ α).symm

theorem ordinalDerived_subtype_finite (A : Set K) (hA : IsClosed A) (α : Ordinal.{u})
    (hfin : (ordinalDerived A α).Finite) : (ordinalDerived (univ : Set A) α).Finite := by
  have h := ordinalDerived_subtype_image A hA α
  rw [← h] at hfin
  exact hfin.of_finite_image Subtype.val_injective.injOn

theorem ordinalDerived_subtype_nonempty (A : Set K) (hA : IsClosed A) (α : Ordinal.{u})
    (hne : (ordinalDerived A α).Nonempty) : (ordinalDerived (univ : Set A) α).Nonempty := by
  rw [← ordinalDerived_subtype_image A hA α, image_nonempty] at hne
  exact hne

theorem ordinalDerived_subtype_ncard (A : Set K) (hA : IsClosed A) (α : Ordinal.{u}) :
    (ordinalDerived (univ : Set A) α).ncard = (ordinalDerived A α).ncard := by
  rw [← ordinalDerived_subtype_image A hA α]
  exact (Set.ncard_image_of_injective _ Subtype.val_injective).symm

theorem ordinalDerived_subtype_singleton (A : Set K) (hA : IsClosed A) (α : Ordinal.{u})
    {p : K} (hp : p ∈ A) (hD : ordinalDerived A α = {p}) :
    ordinalDerived (univ : Set A) α = {⟨p, hp⟩} := by
  have hi := ordinalDerived_subtype_image A hA α
  ext x
  constructor
  · intro hx
    have hv : x.val ∈ ordinalDerived A α := hi ▸ (show x.val ∈
      (Subtype.val : A → K) '' ordinalDerived (univ : Set A) α from ⟨x, hx, rfl⟩)
    rw [hD] at hv
    exact Subtype.ext hv
  · intro hx
    have hval : p ∈ ordinalDerived A α := by rw [hD]; simp
    rw [← hi] at hval
    obtain ⟨y, hy, hyp⟩ := hval
    have hyx : y = x := by
      apply Subtype.ext
      simpa only [show x = ⟨p, hp⟩ from hx] using hyp
    simpa only [hyx] using hy

theorem ordinalDerived_point_not_isolated (α : Ordinal.{u}) (hα : α ≠ 0)
    {p : K} (hp : p ∈ ordinalDerived (univ : Set K) α) : ¬IsOpen ({p} : Set K) := by
  intro ho
  have hm := ordinalDerived_antitone isClosed_univ (Ordinal.one_le_iff_ne_zero.mpr hα) hp
  have hd : p ∈ derivedSet (univ : Set K) := by
    simpa only [← Ordinal.succ_zero, ordinalDerived_succ, ordinalDerived_zero] using hm
  obtain ⟨y, ⟨hy, _⟩, hyp⟩ := (accPt_iff_nhds.mp hd) {p} (ho.mem_nhds (by simp))
  exact hyp (mem_singleton_iff.mp hy)

end ThesisCommon
