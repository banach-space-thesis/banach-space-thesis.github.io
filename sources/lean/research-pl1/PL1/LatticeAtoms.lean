import PL1.LatticeDisjointCountability

/-!
# Positive vector-lattice atoms

These are vector-lattice atoms, not atoms of the underlying partial order.
Atomicity remains an explicit mathematical hypothesis in this development.
-/

noncomputable section
open scoped Topology

namespace PL1

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]

/-- A positive atom has a one-dimensional positive order interval. -/
def IsLatticeAtom (a : E) : Prop :=
  0 < a ∧ ∀ x : E, 0 ≤ x → x ≤ a → ∃ t : ℝ, 0 ≤ t ∧ x = t • a

/-- Every nonzero positive vector dominates a positive vector-lattice atom. -/
def IsAtomicLattice (E : Type*) [NormedAddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [NormedVectorLattice E] : Prop :=
  ∀ u : E, 0 < u → ∃ a : E, IsLatticeAtom a ∧ a ≤ u

namespace IsLatticeAtom

theorem pos {a : E} (ha : IsLatticeAtom a) : 0 < a := ha.1

theorem nonneg {a : E} (ha : IsLatticeAtom a) : 0 ≤ a := ha.pos.le

theorem ne_zero {a : E} (ha : IsLatticeAtom a) : a ≠ 0 := ha.pos.ne'

/-- Positive scalar multiples preserve the actual atom property. -/
theorem smul_pos {a : E} (ha : IsLatticeAtom a) {c : ℝ} (hc : 0 < c) :
    IsLatticeAtom (c • a) := by
  refine ⟨lt_of_le_of_ne (smul_nonneg hc.le ha.nonneg)
    (smul_ne_zero hc.ne' ha.ne_zero).symm, ?_⟩
  intro x hx hxa
  have hdiv : c⁻¹ • x ≤ a := by
    simpa only [inv_smul_smul₀ hc.ne'] using
      smul_le_smul_of_nonneg_left hxa (inv_nonneg.mpr hc.le)
  obtain ⟨t, ht, heq⟩ := ha.2 _ (smul_nonneg (inv_nonneg.mpr hc.le) hx) hdiv
  refine ⟨t, ht, ?_⟩
  have heq' := congrArg (fun z : E => c • z) heq
  simpa only [smul_inv_smul₀ hc.ne', smul_smul, mul_comm c t] using heq'

/-- The atom property applies to every bounded positive multiple interval. -/
theorem eq_smul_of_nonneg_le_smul {a x : E} (ha : IsLatticeAtom a)
    (hx : 0 ≤ x) {c : ℝ} (hc : 0 ≤ c) (hxc : x ≤ c • a) :
    ∃ t : ℝ, 0 ≤ t ∧ x = t • a := by
  rcases hc.eq_or_lt with rfl | hc
  · refine ⟨0, le_rfl, ?_⟩
    simp only [zero_smul] at hxc ⊢
    exact le_antisymm hxc hx
  · obtain ⟨t, ht, heq⟩ := (ha.smul_pos hc).2 x hx hxc
    exact ⟨t * c, mul_nonneg ht hc.le, by simpa only [smul_smul] using heq⟩

theorem normalize {a : E} (ha : IsLatticeAtom a) :
    IsLatticeAtom (‖a‖⁻¹ • a) :=
  ha.smul_pos (inv_pos.mpr (norm_pos_iff.mpr ha.ne_zero))

theorem norm_normalize {a : E} (ha : IsLatticeAtom a) : ‖‖a‖⁻¹ • a‖ = 1 := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha.ne_zero)

/-- Atoms which overlap positively lie on the same positive ray. -/
theorem eq_pos_smul_of_not_isVLDisjoint {a b : E}
    (ha : IsLatticeAtom a) (hb : IsLatticeAtom b) (hd : ¬ IsVLDisjoint a b) :
    ∃ c : ℝ, 0 < c ∧ a = c • b := by
  have hinf : 0 ≤ a ⊓ b := le_inf ha.nonneg hb.nonneg
  have hne : a ⊓ b ≠ 0 := by
    simpa only [IsVLDisjoint, abs_of_nonneg ha.nonneg, abs_of_nonneg hb.nonneg] using hd
  obtain ⟨s, hs, hsa⟩ := ha.2 _ hinf inf_le_left
  obtain ⟨t, ht, htb⟩ := hb.2 _ hinf inf_le_right
  have hs0 : s ≠ 0 := by intro h; apply hne; simpa only [h, zero_smul] using hsa
  have ht0 : t ≠ 0 := by intro h; apply hne; simpa only [h, zero_smul] using htb
  refine ⟨s⁻¹ * t, mul_pos (inv_pos.mpr (lt_of_le_of_ne hs hs0.symm))
    (lt_of_le_of_ne ht ht0.symm), ?_⟩
  have heq := congrArg (fun z : E => s⁻¹ • z) (hsa.symm.trans htb)
  simpa only [inv_smul_smul₀ hs0, smul_smul] using heq

/-- Distinct normalized atoms are lattice-disjoint. -/
theorem isVLDisjoint_of_norm_eq_one {a b : E}
    (ha : IsLatticeAtom a) (hb : IsLatticeAtom b)
    (hna : ‖a‖ = 1) (hnb : ‖b‖ = 1) (hne : a ≠ b) : IsVLDisjoint a b := by
  by_contra hd
  obtain ⟨c, hc, heq⟩ := ha.eq_pos_smul_of_not_isVLDisjoint hb hd
  have hnorm := congrArg norm heq
  rw [hna, norm_smul, hnb, Real.norm_of_nonneg hc.le, mul_one] at hnorm
  exact hne (by simpa only [← hnorm, one_smul] using heq)

end IsLatticeAtom

/-- The actual set of normalized positive atoms. -/
def normalizedLatticeAtoms (E : Type*) [NormedAddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [NormedVectorLattice E] : Set E :=
  {a | IsLatticeAtom a ∧ ‖a‖ = 1}

theorem normalizedLatticeAtoms_pairwise :
    (normalizedLatticeAtoms E).Pairwise IsVLDisjoint := by
  intro a ha b hb hne
  exact ha.1.isVLDisjoint_of_norm_eq_one hb.1 ha.2 hb.2 hne

theorem normalizedLatticeAtoms_countable [TopologicalSpace.SeparableSpace E] :
    (normalizedLatticeAtoms E).Countable :=
  SchurLattice.countable_of_pairwise_isVLDisjoint_norm_one _
    normalizedLatticeAtoms_pairwise (fun _ ha => ha.2)

end PL1
