import BanachIsometric.SignedFiberCount

/-! # Exact excision for the actual integer fiber count -/

namespace BanachIsometric

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem signedFiberCount_congr_source_on_fiber
    (f : E → E) (D : E → E →L[ℝ] E) {s t : Set E} (y : E)
    (h : ∀ x, f x = y → (x ∈ s ↔ x ∈ t)) :
    signedFiberCount f D s y = signedFiberCount f D t y := by
  classical
  have hset : {x : E | x ∈ s ∧ f x = y} = {x : E | x ∈ t ∧ f x = y} := by
    ext x
    constructor
    · intro hx
      exact ⟨(h x hx.2).mp hx.1, hx.2⟩
    · intro hx
      exact ⟨(h x hx.2).mpr hx.1, hx.2⟩
  by_cases hs : {x : E | x ∈ s ∧ f x = y}.Finite
  · have ht : {x : E | x ∈ t ∧ f x = y}.Finite := hset ▸ hs
    have heq := signedFiberSum_congr_source_on_fiber f D y h
    rw [signedFiberSum_eq_coe_signedFiberCount f D s y hs,
      signedFiberSum_eq_coe_signedFiberCount f D t y ht] at heq
    exact_mod_cast heq
  · have ht : ¬ {x : E | x ∈ t ∧ f x = y}.Finite := by
      intro ht
      exact hs (hset.symm ▸ ht)
    simp only [signedFiberCount, dif_neg hs, dif_neg ht]

theorem signedFiberCount_inter_eq_of_fiber_subset
    (f : E → E) (D : E → E →L[ℝ] E) (s R : Set E) (y : E)
    (h : ∀ x ∈ s, f x = y → x ∈ R) :
    signedFiberCount f D (s ∩ R) y = signedFiberCount f D s y := by
  apply signedFiberCount_congr_source_on_fiber f D y
  intro x hxy
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, h x hx hxy⟩⟩

theorem signedFiberCount_eq_zero_of_not_mem_image
    (f : E → E) (D : E → E →L[ℝ] E) (s : Set E) (y : E)
    (hy : y ∉ f '' s) : signedFiberCount f D s y = 0 := by
  classical
  have hset : {x : E | x ∈ s ∧ f x = y} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hy ⟨x, hx.1, hx.2⟩
  have hfin : {x : E | x ∈ s ∧ f x = y}.Finite := hset.symm ▸ finite_empty
  have hz : signedFiberSum f D s y = 0 := by
    letI : IsEmpty {x : E // x ∈ s ∧ f x = y} :=
      ⟨fun x => hy ⟨x.val, x.property.1, x.property.2⟩⟩
    simp only [signedFiberSum, tsum_empty]
  have hc := signedFiberSum_eq_coe_signedFiberCount f D s y hfin
  rw [hz] at hc
  exact_mod_cast hc.symm

end BanachIsometric
