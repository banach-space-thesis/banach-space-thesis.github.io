import ThesisCommon.Analysis.RieszDecomposition
import ThesisCommon.Analysis.PositiveConeExtension
import Mathlib.Analysis.Seminorm

/-! A concrete AL norm from a uniform bound on positive finite
decompositions.  The supremum and its additivity are constructed here.  This
file does not assume an AL representation, and does not assert that the
positive-decomposition bound already follows from an arbitrary Banach-space
isomorphism to ell-one. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]

def positivePartitionValues (x : E) : Set ℝ :=
  {z | ∃ (n : ℕ) (u : Fin n → E), (∀ i, 0 ≤ u i) ∧ (∑ i, u i) ≤ x ∧
    z = ∑ i, ‖u i‖}

def positivePartition (x : E) : ℝ := sSup (positivePartitionValues x)

theorem positivePartitionValues_of_finite {J : Type*} [Fintype J]
    (u : J → E) (hu : ∀ j, 0 ≤ u j) (x : E) (hs : (∑ j, u j) ≤ x) :
    (∑ j, ‖u j‖) ∈ positivePartitionValues x := by
  let e := (Fintype.equivFin J).symm
  have hsum (f : J → E) : (∑ k, f (e k)) = ∑ j, f j :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hnorm : (∑ k, ‖u (e k)‖) = ∑ j, ‖u j‖ :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  refine ⟨Fintype.card J, (fun k => u (e k)), (fun k => hu (e k)), ?_, hnorm.symm⟩
  simpa only [hsum] using hs

theorem positivePartitionValues_zero_mem (x : E) (hx : 0 ≤ x) :
    0 ∈ positivePartitionValues x := by
  refine ⟨0, (fun _ => 0), (fun _ => le_rfl), ?_, ?_⟩ <;> simpa using hx

variable (C : ℝ) (hC : 0 ≤ C)
variable (hbound : ∀ (n : ℕ) (u : Fin n → E), (∀ i, 0 ≤ u i) →
  (∑ i, ‖u i‖) ≤ C * ‖∑ i, u i‖)

include hC hbound in
theorem positivePartitionValues_bdd (x : E) : BddAbove (positivePartitionValues x) := by
  refine ⟨C * ‖x‖, ?_⟩
  rintro z ⟨n,u,hu,hs,rfl⟩
  have hspos : 0 ≤ ∑ i, u i := Finset.sum_nonneg fun i _ => hu i
  have hn : ‖∑ i, u i‖ ≤ ‖x‖ := norm_le_norm_of_abs_le_abs (by
    rw [abs_of_nonneg hspos, abs_of_nonneg (hspos.trans hs)]
    exact hs)
  exact (hbound n u hu).trans (mul_le_mul_of_nonneg_left hn hC)

include hC hbound in
theorem positivePartition_le (x : E) (hx : 0 ≤ x) : positivePartition x ≤ C * ‖x‖ := by
  apply csSup_le ⟨0, positivePartitionValues_zero_mem x hx⟩
  rintro z ⟨n,u,hu,hs,rfl⟩
  have hspos : 0 ≤ ∑ i, u i := Finset.sum_nonneg fun i _ => hu i
  have hn : ‖∑ i, u i‖ ≤ ‖x‖ := norm_le_norm_of_abs_le_abs (by
    rw [abs_of_nonneg hspos, abs_of_nonneg hx]
    exact hs)
  exact (hbound n u hu).trans (mul_le_mul_of_nonneg_left hn hC)

include hC hbound in
theorem norm_le_positivePartition (x : E) (hx : 0 ≤ x) : ‖x‖ ≤ positivePartition x := by
  apply le_csSup (positivePartitionValues_bdd C hC hbound x)
  refine ⟨1, (fun _ => x), (fun _ => hx), ?_, ?_⟩ <;> simp

include hC hbound in
theorem positivePartition_nonneg (x : E) (hx : 0 ≤ x) : 0 ≤ positivePartition x :=
  (norm_nonneg x).trans (norm_le_positivePartition C hC hbound x hx)

include hC hbound in
theorem positivePartition_mono {x y : E} (hx : 0 ≤ x) (hxy : x ≤ y) :
    positivePartition x ≤ positivePartition y := by
  apply csSup_le ⟨0, positivePartitionValues_zero_mem x hx⟩
  rintro z ⟨n,u,hu,hs,rfl⟩
  exact le_csSup (positivePartitionValues_bdd C hC hbound y) ⟨n,u,hu,hs.trans hxy,rfl⟩

include hC hbound in
/-- Riesz decomposition proves the full positive additivity of the actual
supremum; no disjointness or additivity hypothesis is imposed on the old norm. -/
theorem positivePartition_add (x y : E) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    positivePartition (x+y) = positivePartition x + positivePartition y := by
  classical
  apply le_antisymm
  · apply csSup_le ⟨0, positivePartitionValues_zero_mem (x+y) (add_nonneg hx hy)⟩
    rintro z ⟨n,u,hu,hs,rfl⟩
    obtain ⟨a,b,ha,hax,hb,hby,hab⟩ :=
      riesz_split_pair (Finset.sum_nonneg fun i _ => hu i) hx hy hs
    have hau : a ≤ ∑ i, u i := by rw [← hab]; exact le_add_of_nonneg_right hb
    obtain ⟨v,hv,hvs⟩ := riesz_split_finset Finset.univ u (fun i _ => hu i) a ha hau
    have hv0 (i : Fin n) : 0 ≤ v i := (hv i (Finset.mem_univ _)).1
    have huv (i : Fin n) : 0 ≤ u i - v i := sub_nonneg.mpr (hv i (Finset.mem_univ _)).2
    have hrest : (∑ i, (u i - v i)) = b := by rw [Finset.sum_sub_distrib, hvs, ← hab]; abel
    have hxval : (∑ i, ‖v i‖) ≤ positivePartition x :=
      le_csSup (positivePartitionValues_bdd C hC hbound x)
        ⟨n,v,hv0,hvs.le.trans hax,rfl⟩
    have hyval : (∑ i, ‖u i - v i‖) ≤ positivePartition y :=
      le_csSup (positivePartitionValues_bdd C hC hbound y)
        ⟨n,(fun i => u i-v i),huv,hrest.le.trans hby,rfl⟩
    calc
      (∑ i, ‖u i‖) ≤ ∑ i, (‖v i‖ + ‖u i-v i‖) := by
        apply Finset.sum_le_sum
        intro i _
        have h := norm_add_le (v i) (u i-v i)
        simpa only [add_sub_cancel] using h
      _ = (∑ i, ‖v i‖) + ∑ i, ‖u i-v i‖ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add hxval hyval
  · have hpair {r s : ℝ} (hr : r ∈ positivePartitionValues x)
        (hs : s ∈ positivePartitionValues y) :
        r + s ≤ positivePartition (x+y) := by
      obtain ⟨n,u,hu,hux,rfl⟩ := hr
      obtain ⟨m,v,hv,hvy,rfl⟩ := hs
      have hsum : (∑ q : Fin n ⊕ Fin m, Sum.elim u v q) ≤ x+y := by
        simpa only [Fintype.sum_sum_type] using add_le_add hux hvy
      have hmem := positivePartitionValues_of_finite (Sum.elim u v)
        (fun q => by cases q with | inl i => exact hu i | inr j => exact hv j) (x+y) hsum
      have h := le_csSup (positivePartitionValues_bdd C hC hbound (x+y)) hmem
      simpa only [Fintype.sum_sum_type] using h
    have hleft (s : ℝ) (hs : s ∈ positivePartitionValues y) :
        positivePartition x + s ≤ positivePartition (x+y) := by
      apply le_sub_iff_add_le.mp
      apply csSup_le ⟨0, positivePartitionValues_zero_mem x hx⟩
      intro r hr
      exact le_sub_iff_add_le.mpr (hpair hr hs)
    apply le_sub_iff_add_le'.mp
    apply csSup_le ⟨0, positivePartitionValues_zero_mem y hy⟩
    intro s hs
    exact le_sub_iff_add_le'.mpr (hleft s hs)

/-- The additive partition supremum as a genuine continuous functional. -/
def positivePartitionFunctional : E →L[ℝ] ℝ :=
  positiveConeExtension (fun x _ => positivePartition x)
    (positivePartition_add C hC hbound) hC (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (positivePartition_nonneg C hC hbound x hx)]
      exact positivePartition_le C hC hbound x hx)

theorem positivePartitionFunctional_of_nonneg (x : E) (hx : 0 ≤ x) :
    positivePartitionFunctional C hC hbound x = positivePartition x :=
  positiveConeExtension_apply_of_nonneg _ _ _ _ x hx

theorem positivePartitionFunctional_bounds (x : E) (hx : 0 ≤ x) :
    ‖x‖ ≤ positivePartitionFunctional C hC hbound x ∧
    positivePartitionFunctional C hC hbound x ≤ C * ‖x‖ := by
  rw [positivePartitionFunctional_of_nonneg C hC hbound x hx]
  exact ⟨norm_le_positivePartition C hC hbound x hx, positivePartition_le C hC hbound x hx⟩

theorem positivePartitionFunctional_mono {x y : E} (hxy : x ≤ y) :
    positivePartitionFunctional C hC hbound x ≤ positivePartitionFunctional C hC hbound y := by
  have h := (positivePartitionFunctional_bounds C hC hbound (y-x) (sub_nonneg.mpr hxy)).1
  rw [map_sub] at h
  linarith [norm_nonneg (y-x)]

variable [IsOrderedModule ℝ E]

theorem al_lattice_abs_smul (a : ℝ) (x : E) : |a • x| = |a| • |x| := by
  have hpos (r : ℝ) (hr : 0 ≤ r) : |r • x| = r • |x| := by
    by_cases hz : r = 0
    · simp [hz]
    · have h := (OrderIso.smulRight (lt_of_le_of_ne hr (Ne.symm hz)) : E ≃o E).map_sup x (-x)
      change r • (x ⊔ -x) = r • x ⊔ r • (-x) at h
      simpa only [smul_neg, abs] using h.symm
  by_cases ha : 0 ≤ a
  · rw [hpos a ha, abs_of_nonneg ha]
  · have h := hpos (-a) (by linarith)
    simpa only [neg_smul, abs_neg, abs_of_neg (lt_of_not_ge ha)] using h

/-- The concrete equivalent AL norm, recorded as a seminorm together with
the lower bound below, which proves definiteness. -/
def positivePartitionNorm : Seminorm ℝ E := Seminorm.of
  (fun x => positivePartitionFunctional C hC hbound |x|)
  (fun x y => by
    have h := positivePartitionFunctional_mono C hC hbound (abs_add_le x y)
    simpa only [map_add] using h)
  (fun a x => by
    change positivePartitionFunctional C hC hbound |a • x| =
      ‖a‖ * positivePartitionFunctional C hC hbound |x|
    rw [al_lattice_abs_smul, map_smul]
    simp only [smul_eq_mul, Real.norm_eq_abs])

theorem positivePartitionNorm_bounds (x : E) :
    ‖x‖ ≤ positivePartitionNorm C hC hbound x ∧ positivePartitionNorm C hC hbound x ≤ C * ‖x‖ := by
  change ‖x‖ ≤ positivePartitionFunctional C hC hbound |x| ∧
    positivePartitionFunctional C hC hbound |x| ≤ C * ‖x‖
  simpa only [norm_abs_eq_norm] using
    positivePartitionFunctional_bounds C hC hbound |x| (abs_nonneg x)

theorem positivePartitionNorm_add_of_nonneg (x y : E) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    positivePartitionNorm C hC hbound (x+y) =
      positivePartitionNorm C hC hbound x + positivePartitionNorm C hC hbound y := by
  change positivePartitionFunctional C hC hbound |x+y| =
    positivePartitionFunctional C hC hbound |x| + positivePartitionFunctional C hC hbound |y|
  rw [abs_of_nonneg (add_nonneg hx hy), abs_of_nonneg hx, abs_of_nonneg hy, map_add]

end ThesisCommon
