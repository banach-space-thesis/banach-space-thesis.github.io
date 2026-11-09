import PL1.ALOrder
import PL1.LatticeFragments

/-! # Exact fragments in complete AL spaces, without a Schur hypothesis -/

noncomputable section
open Filter Set
open scoped Topology

namespace PL1.ALFragments
open AtomicBandDecomposition SchurLattice LatticeFragments

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]
/-- The principal band of either disjoint piece yields an actual nontrivial
fragment of the original vector. -/
theorem exists_proper_fragment [CompleteSpace E] (hAL : ALRenorming.IsALNorm E)
    (φ : E →L[ℝ] ℝ) (hφ : IsStrictlyPositive φ) {u : E}
    (hu : 0 < u) (hna : ¬ IsLatticeAtom u) :
    ∃ v : E, IsFragment u v ∧ 0 < v ∧ 0 < u - v := by
  obtain ⟨a, b, ha, hau, hb, hbu, hab⟩ := exists_disjoint_nonzero_of_not_atom φ hφ hu hna
  let B := ALOrder.principalBand hAL a
  have hPa : projection B a = a := projection_eq_self B (ALOrder.mem_principalBand_self hAL a)
  have hav : a ≤ projection B u := by
    have h := projection_nonneg B (sub_nonneg.mpr hau)
    rw [map_sub, hPa] at h
    exact sub_nonneg.mp h
  have hbB : b ∈ disjointComplement (B : Set E) := by
    have hgen : (Band.generated ({a} : Set E) : Set E) ⊆ disjointComplement ({b} : Set E) := by
      apply Band.generated_le (B := Band.disjointComplement ({b} : Set E))
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hab
    intro y hy
    have hy' : y ∈ (Band.generated ({a} : Set E) : Set E) := by
      change y ∈ (B : Set E) at hy
      simpa only [B, ALOrder.principalBand_coe] using hy
    exact isVLDisjoint_comm.mp (hgen hy' b rfl)
  have hPb : projection B b = 0 := projection_eq_zero B hbB
  have hbrest : b ≤ u - projection B u := by
    have h := projection_le_self B (sub_nonneg.mpr hbu)
    rw [map_sub, hPb, sub_zero] at h
    exact (le_sub_comm).mp h
  exact ⟨projection B u, fragment_projection B hu.le, ha.trans_le hav, hb.trans_le hbrest⟩

theorem exists_fragment_phi_le_half [CompleteSpace E] (hAL : ALRenorming.IsALNorm E)
    (φ : E →L[ℝ] ℝ) (hφ : IsStrictlyPositive φ) {u : E}
    (hu : 0 < u) (hna : ¬ IsLatticeAtom u) :
    ∃ v : E, IsFragment u v ∧ 0 < v ∧ φ v ≤ φ u / 2 := by
  obtain ⟨v, hv, hvpos, hrpos⟩ := exists_proper_fragment hAL φ hφ hu hna
  by_cases h : φ v ≤ φ u / 2
  · exact ⟨v, hv, hvpos, h⟩
  · refine ⟨u - v, hv.compl, hrpos, ?_⟩
    rw [map_sub]
    linarith

/-- An atomless positive vector has positive fragments of arbitrarily small
strictly-positive-functional mass. -/
theorem exists_small_fragment [CompleteSpace E] (hAL : ALRenorming.IsALNorm E)
    (φ : E →L[ℝ] ℝ) (hφ : IsStrictlyPositive φ) {u : E}
    (hu : 0 < u) (hna : ∀ a : E, IsLatticeAtom a → ¬ a ≤ u)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ v : E, IsFragment u v ∧ 0 < v ∧ φ v < δ := by
  have hseq : ∀ n : ℕ, ∃ v : E, IsFragment u v ∧ 0 < v ∧
      φ v ≤ φ u * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => exact ⟨u, fragment_self hu.le, hu, by simp⟩
    | succ n ih =>
      obtain ⟨w, hw, hwpos, hφw⟩ := ih
      obtain ⟨v, hv, hvpos, hφv⟩ := exists_fragment_phi_le_half hAL φ hφ hwpos
        (fun ha => hna w ha hw.le)
      refine ⟨v, hw.trans hv, hvpos, ?_⟩
      rw [pow_succ]
      nlinarith
  have ht : Tendsto (fun n : ℕ => φ u * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (φ u)
  obtain ⟨n, hn⟩ := (ht.eventually_lt_const hδ).exists
  obtain ⟨v, hv, hvpos, hφv⟩ := hseq n
  exact ⟨v, hv, hvpos, hφv.trans_lt hn⟩

/-- Zorn's lemma and norm convergence of increasing bounded chains produce a
fragment with any prescribed mass in the full scalar interval. -/
theorem exists_fragment_phi_eq [CompleteSpace E] (hAL : ALRenorming.IsALNorm E)
    (φ : E →L[ℝ] ℝ) (hφ : IsStrictlyPositive φ) {u : E}
    (hu : 0 < u) (hna : ∀ a : E, IsLatticeAtom a → ¬ a ≤ u)
    (c : ℝ) (hc : 0 ≤ c) (hcu : c ≤ φ u) :
    ∃ v : E, IsFragment u v ∧ φ v = c := by
  classical
  let S : Set E := {v | IsFragment u v ∧ φ v ≤ c}
  have hzero : (0 : E) ∈ S := ⟨fragment_zero hu.le, by simpa using hc⟩
  obtain ⟨v, hv⟩ := zorn_le₀ S (by
    intro C hCS hchain
    rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, hzero, by simp⟩
    · let : Nonempty C := ⟨⟨hne.choose, hne.choose_spec⟩⟩
      let : IsDirectedOrder C := ⟨fun a b => by
        rcases hchain.total a.property b.property with hab | hba
        · exact ⟨b, hab, le_rfl⟩
        · exact ⟨a, le_rfl, hba⟩⟩
      have hm : Monotone (Subtype.val : C → E) := fun _ _ h => h
      obtain ⟨z, hz⟩ := ALOrder.exists_tendsto_of_monotone_net_norm_bounded hAL
        (Subtype.val : C → E) hm ‖u‖ (by
          intro w
          have hw := (hCS w.property).1
          apply norm_le_norm_of_abs_le_abs
          simpa only [abs_of_nonneg hw.nonneg, abs_of_nonneg hu.le] using hw.le)
      have hzfrag : IsFragment u z := (isClosed_fragments u).mem_of_tendsto hz
        (Eventually.of_forall (fun w => (hCS w.property).1))
      have hzc : φ z ≤ c := le_of_tendsto' ((φ.continuous.tendsto z).comp hz)
        (fun w => (hCS w.property).2)
      refine ⟨z, ⟨hzfrag, hzc⟩, ?_⟩
      intro w hw
      exact (isLUB_of_tendsto_atTop hm hz).1 ⟨⟨w, hw⟩, rfl⟩)
  have hvfrag : IsFragment u v := hv.1.1
  have hvc : φ v ≤ c := hv.1.2
  refine ⟨v, hvfrag, le_antisymm hvc ?_⟩
  by_contra hcv
  have hgap : 0 < c - φ v := sub_pos.mpr (lt_of_not_ge hcv)
  have hr : 0 < u - v := by
    apply lt_of_le_of_ne (sub_nonneg.mpr hvfrag.le)
    intro hz
    have hφz := congrArg φ hz
    rw [map_zero, map_sub] at hφz
    linarith
  have hnr : ∀ a : E, IsLatticeAtom a → ¬ a ≤ u - v :=
    fun a ha har => hna a ha (har.trans hvfrag.compl.le)
  obtain ⟨w, hw, hwpos, hφw⟩ := exists_small_fragment hAL φ hφ hr hnr _ hgap
  have hsum : v + w ∈ S := by
    refine ⟨hvfrag.add_of_compl hw, ?_⟩
    rw [map_add]
    linarith
  have hmax : v + w ≤ v := hv.2 hsum (le_add_of_nonneg_right hw.nonneg)
  have hwle : w ≤ 0 := by
    have h := sub_nonpos.mpr hmax
    simpa only [add_sub_cancel_left] using h
  exact (not_lt_of_ge hwle) hwpos

theorem exists_half_fragment [CompleteSpace E] (hAL : ALRenorming.IsALNorm E)
    (φ : E →L[ℝ] ℝ) (hφ : IsStrictlyPositive φ) {u : E}
    (hu : 0 < u) (hna : ∀ a : E, IsLatticeAtom a → ¬ a ≤ u) :
    ∃ v : E, 0 ≤ v ∧ v ≤ u ∧ IsVLDisjoint v (u - v) ∧ φ v = φ u / 2 := by
  obtain ⟨v, hv, heq⟩ := exists_fragment_phi_eq hAL φ hφ hu hna (φ u / 2)
    (by linarith [hφ u hu]) (by linarith [hφ u hu])
  exact ⟨v, hv.nonneg, hv.le, hv.disjoint, heq⟩

end PL1.ALFragments

