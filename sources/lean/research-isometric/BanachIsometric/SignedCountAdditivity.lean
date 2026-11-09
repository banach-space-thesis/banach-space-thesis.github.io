import BanachIsometric.LipschitzSignedArea
import BanachIsometric.LipschitzNullImages

/-!
# Actual signed-count additivity on compact source pieces

Finite actual fibers split by an explicit disjoint-sum equivalence. For
Lipschitz maps on compact source pieces, their finiteness is derived almost
everywhere from the proved regular-value theorem. Null source overlaps have
null image by the actual Lusin property.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped Topology NNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem signedFiberCount_union_of_finite
    (f : E → E) (D : E → E →L[ℝ] E) (s t : Set E) (y : E)
    (hy : y ∉ f '' (s ∩ t)) (hfin : {x : E | x ∈ s ∪ t ∧ f x = y}.Finite) :
    signedFiberCount f D (s ∪ t) y = signedFiberCount f D s y + signedFiberCount f D t y := by
  classical
  have hs : {x : E | x ∈ s ∧ f x = y}.Finite :=
    hfin.subset (fun x hx => ⟨Or.inl hx.1, hx.2⟩)
  have ht : {x : E | x ∈ t ∧ f x = y}.Finite :=
    hfin.subset (fun x hx => ⟨Or.inr hx.1, hx.2⟩)
  let Fs := {x : E // x ∈ s ∧ f x = y}
  let Ft := {x : E // x ∈ t ∧ f x = y}
  let Fu := {x : E // x ∈ s ∪ t ∧ f x = y}
  letI : Fintype Fs := hs.fintype
  letI : Fintype Ft := ht.fintype
  letI : Fintype Fu := hfin.fintype
  let e : Fs ⊕ Ft ≃ Fu :=
    { toFun := Sum.elim
        (fun x => ⟨x.val, Or.inl x.property.1, x.property.2⟩)
        (fun x => ⟨x.val, Or.inr x.property.1, x.property.2⟩)
      invFun := fun x => if hx : x.val ∈ s then Sum.inl ⟨x.val, hx, x.property.2⟩
        else Sum.inr ⟨x.val, x.property.1.resolve_left hx, x.property.2⟩
      left_inv := by
        intro x
        cases x with
        | inl x =>
            simp only [Sum.elim_inl, dif_pos x.property.1]
            exact congrArg Sum.inl (Subtype.ext rfl)
        | inr x =>
            have hxs : x.val ∉ s := fun hx => hy ⟨x.val, ⟨hx, x.property.1⟩, x.property.2⟩
            simp only [Sum.elim_inr, dif_neg hxs]
            exact congrArg Sum.inr (Subtype.ext rfl)
      right_inv := by
        intro x
        by_cases hx : x.val ∈ s
        · simp only [dif_pos hx, Sum.elim_inl]
          exact Subtype.ext rfl
        · simp only [dif_neg hx, Sum.elim_inr]
          exact Subtype.ext rfl }
  rw [signedFiberCount, dif_pos hfin, signedFiberCount, dif_pos hs, signedFiberCount, dif_pos ht]
  have heq := (Equiv.sum_comp e (fun x : Fu => (SignType.sign (D x.val).det : ℤ))).symm
  simpa only [finiteSignedFiberCount, Fintype.sum_sum_type, e, Sum.elim_inl, Sum.elim_inr] using heq

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem ae_signedFiberCount_union_of_compact
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {C : ℝ≥0} (hf : LipschitzWith C f)
    {s t : Set E} (hs : IsCompact s) (ht : IsCompact t) (hnull : μ (s ∩ t) = 0) :
    ∀ᵐ y ∂μ, signedFiberCount f (fderiv ℝ f) (s ∪ t) y =
      signedFiberCount f (fderiv ℝ f) s y + signedFiberCount f (fderiv ℝ f) t y := by
  have himage : μ (f '' (s ∩ t)) = 0 :=
    lipschitzWith_sends_null_sets_to_null μ μ rfl hf (s ∩ t) hnull
  have hnot : ∀ᵐ y ∂μ, y ∉ f '' (s ∩ t) := by
    apply ae_iff.mpr
    simpa only [not_not, Set.setOf_mem_eq] using himage
  filter_upwards [lipschitzWith_ae_every_preimage_regular μ hf, hnot] with y hy hynot
  have hfin : {x : E | x ∈ s ∪ t ∧ f x = y}.Finite := by
    have hh := finite_actual_regular_fiber (hs.union ht) hf.continuous.continuousOn
      (fun x _hx hxy => hy x hxy)
    simpa only [Set.inter_def, Set.mem_preimage, Set.mem_singleton_iff] using hh
  exact signedFiberCount_union_of_finite f (fderiv ℝ f) s t y hynot hfin

end BanachIsometric
