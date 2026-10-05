import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.LocallyCompact

/-! A concrete model of Alspach's porcupine attachment topology.
The base is K and the locally compact spine X i is attached at anchor i.
The model is a closed subset of K × OnePoint (Σ i, X i), so compactness and
Hausdorffness come from the standard product and one-point constructions.
This is the topology in Alspach (1997), Definition 1.1. -/

noncomputable section
open Set Topology
open scoped OnePoint
namespace Posets
variable {K I : Type*} [TopologicalSpace K]
  (anchor : I → K) (X : I → Type*) [∀ i, TopologicalSpace (X i)]

def alspachGraftCarrier : Set (K × OnePoint (Σ i, X i)) :=
  {p | ∀ z : Σ i, X i, p.2 = (z : OnePoint (Σ i, X i)) → p.1 = anchor z.1}

def AlspachGraft := alspachGraftCarrier anchor X

instance : TopologicalSpace (AlspachGraft anchor X) :=
  inferInstanceAs (TopologicalSpace (alspachGraftCarrier anchor X))

theorem alspachGraftCarrier_isClosed [T1Space K] : IsClosed (alspachGraftCarrier anchor X) := by
  have he : (alspachGraftCarrier anchor X)ᶜ =
      ⋃ i, ({anchor i}ᶜ ×ˢ ((↑) '' Set.range (@Sigma.mk I X i) : Set (OnePoint (Σ i, X i)))) := by
    ext p
    constructor
    · intro hp
      change ¬ ∀ z : Σ i, X i, p.2 = (z : OnePoint (Σ i, X i)) → p.1 = anchor z.1 at hp
      push_neg at hp
      obtain ⟨⟨i, x⟩, hx, hne⟩ := hp
      exact mem_iUnion.mpr ⟨i, hne, ⟨⟨i, x⟩, ⟨x, rfl⟩, hx.symm⟩⟩
    · intro hp hmem
      obtain ⟨i, hne, z, ⟨x, hx⟩, hz⟩ := mem_iUnion.mp hp
      subst z
      exact hne (hmem ⟨i, x⟩ hz.symm)
  rw [← isOpen_compl_iff, he]
  exact isOpen_iUnion fun i => isClosed_singleton.isOpen_compl.prod
    (OnePoint.isOpenMap_coe _ isOpen_range_sigmaMk)

instance [CompactSpace K] [T1Space K] : CompactSpace (AlspachGraft anchor X) :=
  isCompact_iff_compactSpace.mp (alspachGraftCarrier_isClosed anchor X).isCompact

instance alspachSigmaWeaklyLocallyCompact [∀ i, WeaklyLocallyCompactSpace (X i)] :
    WeaklyLocallyCompactSpace (Σ i, X i) where
  exists_compact_mem_nhds z := by
    obtain ⟨U, hU, hz⟩ := exists_compact_mem_nhds z.2
    exact ⟨Sigma.mk z.1 '' U, hU.image continuous_sigmaMk,
      isOpenMap_sigmaMk.image_mem_nhds hz⟩

instance [T2Space K] [∀ i, T2Space (X i)] [∀ i, LocallyCompactSpace (X i)] :
    T2Space (AlspachGraft anchor X) :=
  inferInstanceAs (T2Space (alspachGraftCarrier anchor X))

instance [Countable K] [Countable I] [∀ i, Countable (X i)] :
    Countable (AlspachGraft anchor X) := by
  letI : Countable (OnePoint (Σ i, X i)) := inferInstanceAs (Countable (Option (Σ i, X i)))
  exact inferInstanceAs (Countable (alspachGraftCarrier anchor X))

def alspachGraftBase (k : K) : AlspachGraft anchor X :=
  ⟨(k, ∞), by intro z hz; exact (OnePoint.coe_ne_infty z hz.symm).elim⟩

def alspachGraftSpine (z : Σ i, X i) : AlspachGraft anchor X :=
  ⟨(anchor z.1, (z : OnePoint (Σ i, X i))), by
    intro w hw
    exact congrArg (fun v : Σ i, X i => anchor v.1) (OnePoint.coe_injective hw)⟩

def alspachGraftProjection (p : AlspachGraft anchor X) : OnePoint (Σ i, X i) := p.val.2

theorem alspachGraftBase_continuous : Continuous (alspachGraftBase anchor X) :=
  (continuous_id.prodMk continuous_const).subtype_mk _

theorem alspachGraftBase_injective : Function.Injective (alspachGraftBase anchor X) := by
  intro x y h
  exact congrArg (fun p : AlspachGraft anchor X => p.val.1) h

theorem alspachGraftSpine_injective : Function.Injective (alspachGraftSpine anchor X) := by
  intro x y h
  exact OnePoint.coe_injective (congrArg (alspachGraftProjection anchor X) h)

theorem alspachGraftSpine_continuous : Continuous (alspachGraftSpine anchor X) := by
  apply continuous_sigma
  intro i
  have h : Continuous (fun x : X i => (⟨i, x⟩ : Σ i, X i)) := continuous_sigmaMk
  have hk : Continuous (fun _ : X i => anchor i) := continuous_const
  exact (hk.prodMk (OnePoint.continuous_coe.comp h)).subtype_mk _

theorem alspachGraftProjection_continuous : Continuous (alspachGraftProjection anchor X) :=
  continuous_snd.comp continuous_subtype_val

theorem alspachGraftSpine_image (U : Set (Σ i, X i)) :
    alspachGraftSpine anchor X '' U =
      alspachGraftProjection anchor X ⁻¹' ((↑) '' U) := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, hp⟩
    refine ⟨z, hz, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact (p.property z hp.symm).symm
    · exact hp

theorem alspachGraftSpine_isOpenEmbedding : IsOpenEmbedding (alspachGraftSpine anchor X) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (alspachGraftSpine_continuous anchor X) (alspachGraftSpine_injective anchor X)
  intro U hU
  rw [alspachGraftSpine_image]
  exact (OnePoint.isOpenMap_coe U hU).preimage (alspachGraftProjection_continuous anchor X)

theorem alspachGraftBase_isClosedEmbedding [CompactSpace K] [T2Space K]
    [∀ i, T2Space (X i)] [∀ i, LocallyCompactSpace (X i)] :
    IsClosedEmbedding (alspachGraftBase anchor X) :=
  (alspachGraftBase_continuous anchor X).isClosedEmbedding
    (alspachGraftBase_injective anchor X)

theorem alspachGraft_cases (p : AlspachGraft anchor X) :
    (∃ k, p = alspachGraftBase anchor X k) ∨
      ∃ z, p = alspachGraftSpine anchor X z := by
  rcases p with ⟨⟨k, z⟩, hp⟩
  cases z with
  | infty => exact Or.inl ⟨k, rfl⟩
  | coe z =>
      right
      refine ⟨z, ?_⟩
      apply Subtype.ext
      exact Prod.ext (hp z rfl) rfl

end Posets
