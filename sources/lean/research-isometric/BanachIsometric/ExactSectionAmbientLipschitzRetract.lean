import BanachIsometric.ExactSectionCompactTotalSpace
import BanachIsometric.ExactSectionLipschitzNeighborhood
import BanachIsometric.LipschitzNormalization
import BanachIsometric.SmoothSphereLipschitz
import Mathlib.Topology.MetricSpace.Thickening

/-! The actual exact-section total space over the round sphere is a Lipschitz
retract of a compact neighborhood in the original real vector space of pairs
of a normal vector and a section operator. -/

noncomputable section
namespace BanachIsometric.ExactSectionPrincipalData

open Set Metric MeasureTheory NormedSpace
open scoped Topology NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {m : ℕ} {p : F → ℝ} {H : sphere (0 : F) 1 → Submodule ℝ F}
    {a₀ : sphere (0 : F) 1} (D : ExactSectionPrincipalData m p H a₀)

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "V" => F × (E →L[ℝ] F)
local notation "Total" => ExactSectionSpace D.ModelBody (fun y : F => p y ≤ 1) H

def ambientExactSectionInclusion : Total → V := fun t => (t.val.1.val, t.val.2)

omit [FiniteDimensional ℝ F] in
theorem ambientExactSectionInclusion_isometry : Isometry D.ambientExactSectionInclusion :=
  isometry_iff_dist_eq.mpr (fun _ _ => rfl)

omit [FiniteDimensional ℝ F] in
theorem ambientExactSectionInclusion_lipschitz :
    LipschitzWith 1 D.ambientExactSectionInclusion := D.ambientExactSectionInclusion_isometry.lipschitz

/-- This neighborhood and retraction are for the literal operator-and-normal
subset. In particular, its values represent the same original body sections. -/
theorem exists_lipschitz_ambient_neighborhood_retraction
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C L : ℝ≥0}
    (hC : LipschitzOnWith C p (sphere (0 : F) 1))
    (hProj : LipschitzWith L (fun a => (H a).starProjection)) :
    ∃ A : Set V, IsCompact A ∧ ∃ r : A → Total,
      (∃ K : ℝ≥0, LipschitzWith K r) ∧
      ∀ t : Total, ∃ ht : D.ambientExactSectionInclusion t ∈ interior A,
        r ⟨D.ambientExactSectionInclusion t, interior_subset ht⟩ = t := by
  obtain ⟨hS, hreg, h0⟩ := D.modelBody_geometric_properties hp hC
  obtain ⟨R⟩ := nonempty_ambientBodyRetraction μ D.ModelBody hS hreg h0
  obtain ⟨U, r, hU, hrLocal, hrIn, hrRange, hrFix⟩ :=
    D.atlas.exists_locallyLipschitz_fiberwise_neighborhood_retraction R hProj
  let X : Set V := {q | (1 / 2 : ℝ) < ‖q.1‖}
  have hX : IsOpen X := isOpen_lt continuous_const (continuous_norm.comp continuous_fst)
  have hf : LipschitzWith 1 (fun x : X => x.val.1) := by
    simpa only [mul_one] using LipschitzWith.prod_fst.comp (LipschitzWith.subtype_val X)
  have hs : LipschitzWith 1 (fun x : X => x.val.2) := by
    simpa only [mul_one] using LipschitzWith.prod_snd.comp (LipschitzWith.subtype_val X)
  have hhalf : (0 : ℝ≥0) < 1 / 2 := by norm_num
  have hnormalize := lipschitzWith_normalize_of_lower_bound hf hhalf
    (fun x : X => by simpa using (show (1 / 2 : ℝ) ≤ ‖x.val.1‖ from x.property.le))
  have hne (x : X) : x.val.1 ≠ 0 := by
    intro hx
    have h := x.property
    change (1 / 2 : ℝ) < ‖x.val.1‖ at h
    rw [hx, norm_zero] at h
    norm_num at h
  let q : X → sphere (0 : F) 1 × (E →L[ℝ] F) := fun x =>
    (⟨normalize x.val.1, by
      rw [mem_sphere_zero_iff_norm]
      exact norm_normalize (hne x)⟩, x.val.2)
  have hq : ∃ K : ℝ≥0, LipschitzWith K q :=
    ⟨_, (hnormalize.subtype_mk (fun x => (q x).1.property)).prodMk hs⟩
  obtain ⟨Kq, hqLip⟩ := hq
  let O : Set V := Subtype.val '' (q ⁻¹' U)
  have hO : IsOpen O := hX.isOpenEmbedding_subtypeVal.isOpenMap _
    (hU.preimage hqLip.continuous)
  have hOX : O ⊆ X := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hqFix (t : Total) (ht : D.ambientExactSectionInclusion t ∈ X) :
      q ⟨D.ambientExactSectionInclusion t, ht⟩ = t.val := by
    apply Prod.ext
    · apply Subtype.ext
      exact normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere t.val.1)
    · rfl
  have htX (t : Total) : D.ambientExactSectionInclusion t ∈ X := by
    change (1 / 2 : ℝ) < ‖t.val.1.val‖
    rw [norm_eq_of_mem_sphere t.val.1]
    norm_num
  have htO (t : Total) : D.ambientExactSectionInclusion t ∈ O :=
    ⟨⟨_, htX t⟩, by simpa only [mem_preimage, hqFix] using hrIn t, rfl⟩
  let T : Set V := range D.ambientExactSectionInclusion
  letI : CompactSpace Total := D.compactSpace_actualTotalSpace μ hp hC
  have hT : IsCompact T := isCompact_range D.ambientExactSectionInclusion_lipschitz.continuous
  obtain ⟨δ, hδ, hδO⟩ := hT.exists_cthickening_subset_open hO (by rintro _ ⟨t, rfl⟩; exact htO t)
  let A := cthickening δ T
  have hA : IsCompact A := hT.cthickening
  have htA (t : Total) : D.ambientExactSectionInclusion t ∈ interior A :=
    thickening_subset_interior_cthickening δ T (self_subset_thickening hδ T ⟨t, rfl⟩)
  let a : A → X := fun x => ⟨x.val, hOX (hδO x.property)⟩
  have ha : LipschitzWith 1 a := (LipschitzWith.subtype_val A).subtype_mk (fun x => (a x).property)
  have hqa : LipschitzWith (Kq * 1) (q ∘ a) := hqLip.comp ha
  have haU (x : A) : q (a x) ∈ U := by
    obtain ⟨y, hy, hxy⟩ := hδO x.property
    have he : y = a x := Subtype.ext hxy
    exact he ▸ hy
  let f : A → Total := fun x => ⟨((q (a x)).1, r (q (a x))), hrRange _ (haU x)⟩
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hfLip : ∃ B : ℝ≥0, LipschitzWith B f := by
    apply exists_lipschitzWith_of_local_on_compact f
    intro x
    obtain ⟨W, hWo, hxW, _hWU, B, hB⟩ := hrLocal _ (haU x)
    let W' := (q ∘ a) ⁻¹' W
    have hxW' : W' ∈ 𝓝 x := (hWo.preimage hqa.continuous).mem_nhds hxW
    have hmap : MapsTo (q ∘ a) W' W := fun _ h => h
    have hprod := (LipschitzWith.prod_fst.comp hqa).lipschitzOnWith.prodMk
      (hB.comp hqa.lipschitzOnWith hmap)
    refine ⟨max (1 * (Kq * 1)) (B * (Kq * 1)), W', hxW', LipschitzOnWith.of_dist_le_mul ?_⟩
    intro y hy z hz
    exact hprod.dist_le_mul y hy z hz
  refine ⟨A, hA, f, hfLip, fun t => ⟨htA t, ?_⟩⟩
  apply Subtype.ext
  change ((q (a ⟨D.ambientExactSectionInclusion t, interior_subset (htA t)⟩)).1,
    r (q (a ⟨D.ambientExactSectionInclusion t, interior_subset (htA t)⟩))) = t.val
  rw [show q (a ⟨D.ambientExactSectionInclusion t, interior_subset (htA t)⟩) = t.val from hqFix t _]
  exact Prod.ext rfl (hrFix t)

end BanachIsometric.ExactSectionPrincipalData
