import Posets.SzlenkOperator

/-! Compact perturbation estimates for the Szlenk derivation, used in the
norm-closedness argument of Brooker, Theorem 2.2 and Lemma 2.7. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Topology
namespace Posets
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Compactness of the second coordinate lifts closure through projection. -/
theorem exists_mem_closure_prod_of_compact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {H : Set (X × Y)} {x : X} (hx : x ∈ closure (Prod.fst '' H)) :
    ∃ y : Y, (x, y) ∈ closure H := by
  have hx' : x ∈ Prod.fst '' closure H :=
    closure_minimal (Set.image_mono subset_closure)
      (isClosedMap_fst_of_compactSpace (closure H) isClosed_closure) hx
  obtain ⟨⟨a, y⟩, hy, heq⟩ := hx'
  change a = x at heq
  exact ⟨y, heq ▸ hy⟩

theorem weakStar_norm_sub_isClosed (δ : ℝ) :
    IsClosed {p : WeakDual 𝕜 E × WeakDual 𝕜 E |
      ‖WeakDual.toStrongDual p.1 - WeakDual.toStrongDual p.2‖ ≤ δ} := by
  have h := (WeakDual.isClosed_closedBall (𝕜 := 𝕜) (E := E) 0 δ).preimage
    (continuous_fst.sub continuous_snd : Continuous
      (fun p : WeakDual 𝕜 E × WeakDual 𝕜 E => p.1 - p.2))
  convert h using 1
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
    map_sub]

theorem szlenkDeriv_exists_far {ε : ℝ} {K : Set (WeakDual 𝕜 E)}
    {x : WeakDual 𝕜 E} (hx : x ∈ szlenkDeriv ε K)
    {U : Set (WeakDual 𝕜 E)} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ a ∈ K ∩ U, ε / 2 < ‖WeakDual.toStrongDual a - WeakDual.toStrongDual x‖ := by
  obtain ⟨a, ha, b, hb, hab⟩ := hx.2 U hU hxU
  by_contra hn
  push_neg at hn
  have ha' := hn a ha
  have hb' := hn b hb
  have htri := dist_triangle (WeakDual.toStrongDual a)
    (WeakDual.toStrongDual x) (WeakDual.toStrongDual b)
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (WeakDual.toStrongDual x) (WeakDual.toStrongDual b)] at htri
  linarith only [ha', hb', htri, hab]

/-- One derivative preserves proximity, at a reduced derivative scale.
Compactness is required only for the approximating set L. -/
theorem szlenkDeriv_perturbation {ε η δ : ℝ} {K L : Set (WeakDual 𝕜 E)}
    (hL : IsCompact L) (hscale : η + 2 * δ ≤ ε / 2)
    (hnear : ∀ a ∈ K, ∃ b ∈ L,
      ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ ≤ δ)
    {x : WeakDual 𝕜 E} (hx : x ∈ szlenkDeriv ε K) :
    ∃ y ∈ szlenkDeriv η L,
      ‖WeakDual.toStrongDual x - WeakDual.toStrongDual y‖ ≤ δ := by
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let G : Set (WeakDual 𝕜 E) :=
    {a | a ∈ K ∧ ε / 2 < ‖WeakDual.toStrongDual a - WeakDual.toStrongDual x‖}
  let H : Set (WeakDual 𝕜 E × L) :=
    {p | p.1 ∈ G ∧ ‖WeakDual.toStrongDual p.1 - WeakDual.toStrongDual p.2.val‖ ≤ δ}
  have hxG : x ∈ closure G := mem_closure_iff.mpr (by
    intro U hU hxU
    obtain ⟨a, ha, hafar⟩ := szlenkDeriv_exists_far hx hU hxU
    exact ⟨a, ha.2, ha.1, hafar⟩)
  have hGH : G ⊆ Prod.fst '' H := by
    intro a ha
    obtain ⟨b, hb, hdist⟩ := hnear a ha.1
    exact ⟨(a, ⟨b, hb⟩), ⟨ha, hdist⟩, rfl⟩
  obtain ⟨y, hxy⟩ : ∃ y : L, (x, y) ∈ closure H :=
    exists_mem_closure_prod_of_compact (closure_mono hGH hxG)
  have hclosed : IsClosed {p : WeakDual 𝕜 E × L |
      ‖WeakDual.toStrongDual p.1 - WeakDual.toStrongDual p.2.val‖ ≤ δ} := by
    let f : WeakDual 𝕜 E × L → WeakDual 𝕜 E × WeakDual 𝕜 E :=
      fun p => (p.1, p.2.val)
    have hf : Continuous f := continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd)
    exact (weakStar_norm_sub_isClosed (𝕜 := 𝕜) (E := E) δ).preimage hf
  have hHR : H ⊆ {p : WeakDual 𝕜 E × L |
      ‖WeakDual.toStrongDual p.1 - WeakDual.toStrongDual p.2.val‖ ≤ δ} :=
    fun _ hp => hp.2
  have hxyR := closure_minimal hHR hclosed hxy
  have hdist : ‖WeakDual.toStrongDual x - WeakDual.toStrongDual y.val‖ ≤ δ := hxyR
  refine ⟨y.val, ⟨y.property, ?_⟩, hdist⟩
  intro V hV hyV
  let W : Set (WeakDual 𝕜 E × L) := {p | p.2.val ∈ V}
  have hW : IsOpen W := hV.preimage (continuous_subtype_val.comp continuous_snd)
  obtain ⟨⟨a, b⟩, hbV, hab⟩ := mem_closure_iff.mp hxy W hW hyV
  have htri := dist_triangle4 (WeakDual.toStrongDual a) (WeakDual.toStrongDual b.val)
    (WeakDual.toStrongDual y.val) (WeakDual.toStrongDual x)
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (WeakDual.toStrongDual y.val) (WeakDual.toStrongDual x)] at htri
  refine ⟨b.val, ⟨b.property, hbV⟩, y.val, ⟨y.property, hyV⟩, ?_⟩
  have hfar := hab.1.2
  have hclose := hab.2
  linarith only [hfar, hclose, hdist, htri, hscale]

end Posets
