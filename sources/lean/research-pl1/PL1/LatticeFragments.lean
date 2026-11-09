import PL1.AtomicBandDecomposition
import PL1.LatticeStrictPositive
import Mathlib.Order.Zorn

/-! # Genuine disjoint fragments of positive lattice vectors -/

noncomputable section
open Filter Set
open scoped Topology

namespace PL1.LatticeFragments
open AtomicBandDecomposition SchurLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]

/-- A positive fragment of u, with disjoint positive remainder. -/
def IsFragment (u v : E) : Prop := 0 ≤ v ∧ v ≤ u ∧ IsVLDisjoint v (u - v)

omit [IsOrderedAddMonoid E] [NormedVectorLattice E] in
theorem IsFragment.nonneg {u v : E} (h : IsFragment u v) : 0 ≤ v := h.1
omit [IsOrderedAddMonoid E] [NormedVectorLattice E] in
theorem IsFragment.le {u v : E} (h : IsFragment u v) : v ≤ u := h.2.1
omit [IsOrderedAddMonoid E] [NormedVectorLattice E] in
theorem IsFragment.disjoint {u v : E} (h : IsFragment u v) : IsVLDisjoint v (u - v) := h.2.2

omit [NormedVectorLattice E] in
theorem fragment_zero {u : E} (hu : 0 ≤ u) : IsFragment u 0 :=
  ⟨le_rfl, hu, isVLDisjoint_zero_left _⟩

omit [NormedVectorLattice E] in
theorem fragment_self {u : E} (hu : 0 ≤ u) : IsFragment u u :=
  ⟨hu, le_rfl, by simpa using isVLDisjoint_zero_right u⟩

omit [NormedVectorLattice E] in
theorem IsFragment.compl {u v : E} (h : IsFragment u v) : IsFragment u (u - v) := by
  refine ⟨sub_nonneg.mpr h.le, sub_le_self _ h.nonneg, ?_⟩
  simpa only [sub_sub_cancel] using isVLDisjoint_comm.mp h.disjoint

omit [NormedVectorLattice E] in
theorem IsFragment.trans {u v w : E} (hv : IsFragment u v) (hw : IsFragment v w) :
    IsFragment u w := by
  refine ⟨hw.nonneg, hw.le.trans hv.le, ?_⟩
  have hd : IsVLDisjoint w (u - v) := hv.disjoint.mono_left (by
    simpa only [abs_of_nonneg hw.nonneg, abs_of_nonneg hv.nonneg] using hw.le)
  have he : u - w = (u - v) + (v - w) := by abel
  rw [he]
  exact hd.add_right hw.disjoint

omit [NormedVectorLattice E] in
theorem IsFragment.add_of_compl {u v w : E} (hv : IsFragment u v)
    (hw : IsFragment (u - v) w) : IsFragment u (v + w) := by
  have hvw : v + w ≤ u := by
    have hh : w + v ≤ u := le_sub_iff_add_le.mp hw.le
    simpa only [add_comm] using hh
  refine ⟨add_nonneg hv.nonneg hw.nonneg, hvw, ?_⟩
  have he : u - (v + w) = (u - v) - w := by abel
  rw [he]
  exact (hv.disjoint.mono_right (by
    rw [abs_of_nonneg (sub_nonneg.mpr hw.le), abs_of_nonneg (sub_nonneg.mpr hv.le)]
    exact sub_le_self _ hw.nonneg)).add_left hw.disjoint

theorem isClosed_fragments (u : E) : IsClosed {v | IsFragment u v} := by
  have hab : Continuous (|·| : E → E) := NormedVectorLattice.lipschitzWith_abs.continuous
  have hc : Continuous (fun v : E => |v| ⊓ |u - v|) :=
    hab.inf (hab.comp (continuous_const.sub continuous_id))
  exact isClosed_Ici.inter (isClosed_Iic.inter (isClosed_eq hc continuous_const))

theorem fragment_projection (B : ProjectionBand E) {u : E} (hu : 0 ≤ u) :
    IsFragment u (projection B u) := by
  refine ⟨projection_nonneg B hu, projection_le_self B hu, ?_⟩
  exact isVLDisjoint_comm.mp (B.id_sub_bandProjection_mem u _ (projection_mem B u))

theorem phi_mono (φ : E →L[ℝ] ℝ) (hφ : IsStrictlyPositive φ) {x y : E} (hxy : x ≤ y) :
    φ x ≤ φ y := by
  have hp := StrongDual.apply_nonneg_of_nonneg hφ.nonneg (sub_nonneg.mpr hxy)
  rw [map_sub] at hp
  exact sub_nonneg.mp hp

/-- A nonatom has two disjoint nonzero positive vectors below it. A strictly
positive functional chooses the scalar separating their positive parts. -/
theorem exists_disjoint_nonzero_of_not_atom (φ : E →L[ℝ] ℝ)
    (hφ : IsStrictlyPositive φ) {u : E} (hu : 0 < u) (hna : ¬ IsLatticeAtom u) :
    ∃ a b : E, 0 < a ∧ a ≤ u ∧ 0 < b ∧ b ≤ u ∧ IsVLDisjoint a b := by
  classical
  have hbad : ¬ ∀ x : E, 0 ≤ x → x ≤ u → ∃ t : ℝ, 0 ≤ t ∧ x = t • u :=
    fun h => hna ⟨hu, h⟩
  push Not at hbad
  obtain ⟨x, hx, hxu, hbad⟩ := hbad
  let t : ℝ := φ x / φ u
  have hφu : 0 < φ u := hφ u hu
  have ht : 0 ≤ t := div_nonneg (StrongDual.apply_nonneg_of_nonneg hφ.nonneg hx) hφu.le
  have ht1 : t ≤ 1 := (div_le_one hφu).mpr (phi_mono φ hφ hxu)
  let z : E := x - t • u
  have hz : z ≠ 0 := by
    intro he
    exact hbad t ht (sub_eq_zero.mp he)
  have hφz : φ z = 0 := by
    simp only [z, t, map_sub, map_smul, smul_eq_mul]
    field_simp [hφu.ne']
    ring
  have he : φ z⁺ = φ z⁻ := by
    have h := congrArg φ (posPart_sub_negPart z)
    rw [map_sub, hφz] at h
    exact sub_eq_zero.mp h
  have hp : z⁺ ≠ 0 := by
    intro h
    have hφn : φ z⁻ = 0 := by rw [← he, h, map_zero]
    have hn := hφ.eq_zero_of_nonneg (negPart_nonneg z) hφn
    exact hz (by rw [← posPart_sub_negPart z, h, hn, sub_self])
  have hn : z⁻ ≠ 0 := by
    intro h
    have hφp : φ z⁺ = 0 := by rw [he, h, map_zero]
    exact hp (hφ.eq_zero_of_nonneg (posPart_nonneg z) hφp)
  have htu : t • u ≤ u := by simpa only [one_smul] using
    smul_le_smul_of_nonneg_right ht1 hu.le
  have hpbound : z⁺ ≤ u := sup_le ((sub_le_self _ (smul_nonneg ht hu.le)).trans hxu) hu.le
  have hnbound : z⁻ ≤ u := sup_le (by
    change -(x - t • u) ≤ u
    rw [neg_sub]
    exact (sub_le_self _ hx).trans htu) hu.le
  exact ⟨z⁺, z⁻, lt_of_le_of_ne (posPart_nonneg z) hp.symm, hpbound,
    lt_of_le_of_ne (negPart_nonneg z) hn.symm, hnbound,
    isVLDisjoint_of_inf_eq_zero (posPart_inf_negPart_eq_zero z)⟩

/-- The principal band of either disjoint piece yields an actual nontrivial
fragment of the original vector. -/
theorem exists_proper_fragment [CompleteSpace E] (hS : HasSchurProperty ℝ E)
    (φ : E →L[ℝ] ℝ) (hφ : IsStrictlyPositive φ) {u : E}
    (hu : 0 < u) (hna : ¬ IsLatticeAtom u) :
    ∃ v : E, IsFragment u v ∧ 0 < v ∧ 0 < u - v := by
  obtain ⟨a, b, ha, hau, hb, hbu, hab⟩ := exists_disjoint_nonzero_of_not_atom φ hφ hu hna
  let B := principalBand hS a
  have hPa : projection B a = a := projection_eq_self B (mem_principalBand_self hS a)
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
      simpa only [B, principalBand_coe] using hy
    exact isVLDisjoint_comm.mp (hgen hy' b rfl)
  have hPb : projection B b = 0 := projection_eq_zero B hbB
  have hbrest : b ≤ u - projection B u := by
    have h := projection_le_self B (sub_nonneg.mpr hbu)
    rw [map_sub, hPb, sub_zero] at h
    exact (le_sub_comm).mp h
  exact ⟨projection B u, fragment_projection B hu.le, ha.trans_le hav, hb.trans_le hbrest⟩

theorem exists_fragment_phi_le_half [CompleteSpace E] (hS : HasSchurProperty ℝ E)
    (φ : E →L[ℝ] ℝ) (hφ : IsStrictlyPositive φ) {u : E}
    (hu : 0 < u) (hna : ¬ IsLatticeAtom u) :
    ∃ v : E, IsFragment u v ∧ 0 < v ∧ φ v ≤ φ u / 2 := by
  obtain ⟨v, hv, hvpos, hrpos⟩ := exists_proper_fragment hS φ hφ hu hna
  by_cases h : φ v ≤ φ u / 2
  · exact ⟨v, hv, hvpos, h⟩
  · refine ⟨u - v, hv.compl, hrpos, ?_⟩
    rw [map_sub]
    linarith

/-- An atomless positive vector has positive fragments of arbitrarily small
strictly-positive-functional mass. -/
theorem exists_small_fragment [CompleteSpace E] (hS : HasSchurProperty ℝ E)
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
      obtain ⟨v, hv, hvpos, hφv⟩ := exists_fragment_phi_le_half hS φ hφ hwpos
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
theorem exists_fragment_phi_eq [CompleteSpace E] (hS : HasSchurProperty ℝ E)
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
      obtain ⟨z, hz⟩ := exists_tendsto_of_monotone_net_norm_bounded hS
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
  obtain ⟨w, hw, hwpos, hφw⟩ := exists_small_fragment hS φ hφ hr hnr _ hgap
  have hsum : v + w ∈ S := by
    refine ⟨hvfrag.add_of_compl hw, ?_⟩
    rw [map_add]
    linarith
  have hmax : v + w ≤ v := hv.2 hsum (le_add_of_nonneg_right hw.nonneg)
  have hwle : w ≤ 0 := by
    have h := sub_nonpos.mpr hmax
    simpa only [add_sub_cancel_left] using h
  exact (not_lt_of_ge hwle) hwpos

theorem exists_half_fragment [CompleteSpace E] (hS : HasSchurProperty ℝ E)
    (φ : E →L[ℝ] ℝ) (hφ : IsStrictlyPositive φ) {u : E}
    (hu : 0 < u) (hna : ∀ a : E, IsLatticeAtom a → ¬ a ≤ u) :
    ∃ v : E, 0 ≤ v ∧ v ≤ u ∧ IsVLDisjoint v (u - v) ∧ φ v = φ u / 2 := by
  obtain ⟨v, hv, heq⟩ := exists_fragment_phi_eq hS φ hφ hu hna (φ u / 2)
    (by linarith [hφ u hu]) (by linarith [hφ u hu])
  exact ⟨v, hv.nonneg, hv.le, hv.disjoint, heq⟩

end PL1.LatticeFragments
