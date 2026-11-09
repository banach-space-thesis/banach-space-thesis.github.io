import BanachIsometric.FiniteNerveRationalCoordinates

/-! The actual normalization projection from weakly ordered chains to ordinary
strict ordered-face chains. Degenerate tuples are killed. Its chain relation
is proved by cancellation of the two deletions at an adjacent repeated vertex.
No normalized-chain equivalence is assumed. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

variable {ι : Type} [LinearOrder ι] [Fintype ι]

theorem exists_adjacent_eq_of_not_strict {K : Complex ι} {n : ℕ}
    (v : OrderedSimplex K (n + 1)) (hv : ¬ StrictMono v.val) :
    ∃ i : Fin (n + 1), v.val i.castSucc = v.val i.succ := by
  have hn : ¬ ∀ i : Fin (n + 1), v.val i.castSucc < v.val i.succ :=
    fun h => hv (Fin.strictMono_iff_lt_succ.mpr h)
  obtain ⟨i, hi⟩ := not_forall.mp hn
  exact ⟨i, le_antisymm (v.val.monotone (Fin.castSucc_lt_succ i).le) (le_of_not_gt hi)⟩

theorem orderedFace_eq_of_adjacent_eq {K : Complex ι} {n : ℕ}
    (v : OrderedSimplex K (n + 1)) (i : Fin (n + 1))
    (hi : v.val i.castSucc = v.val i.succ) :
    orderedFace K i.castSucc v = orderedFace K i.succ v := by
  apply Subtype.ext
  apply OrderHom.ext
  funext j
  rcases lt_trichotomy j i with hj | rfl | hj
  · simp only [orderedFace_apply, Fin.succAbove_castSucc_of_lt _ _ hj,
      Fin.succAbove_succ_of_le _ _ hj.le]
  · simpa only [orderedFace_apply, Fin.succAbove_castSucc_self,
      Fin.succAbove_succ_self] using hi.symm
  · simp only [orderedFace_apply, Fin.succAbove_castSucc_of_le _ _ hj.le,
      Fin.succAbove_succ_of_lt _ _ hj]

theorem not_strictMono_orderedFace_of_adjacent_eq {K : Complex ι} {n : ℕ}
    (v : OrderedSimplex K (n + 1)) (i : Fin (n + 1))
    (hi : v.val i.castSucc = v.val i.succ) (j : Fin (n + 2))
    (hj₀ : j ≠ i.castSucc) (hj₁ : j ≠ i.succ) :
    ¬ StrictMono (orderedFace K j v).val := by
  intro hstrict
  have h₀ : i.castSucc ∈ Set.range j.succAbove := by
    rw [Fin.range_succAbove]
    exact Ne.symm hj₀
  have h₁ : i.succ ∈ Set.range j.succAbove := by
    rw [Fin.range_succAbove]
    exact Ne.symm hj₁
  obtain ⟨a, ha⟩ := h₀
  obtain ⟨b, hb⟩ := h₁
  have he : (orderedFace K j v).val a = (orderedFace K j v).val b := by
    change v.val (j.succAbove a) = v.val (j.succAbove b)
    rw [ha, hb]
    exact hi
  have hab := hstrict.injective he
  have heq : i.castSucc = i.succ := by rw [← ha, ← hb, hab]
  exact (ne_of_lt (Fin.castSucc_lt_succ i)) heq

def strictChainProjection (K : Complex ι) (n : ℕ) :
    WeakRationalChains K n →ₗ[ℚ] FiniteRationalChains K n :=
  Finsupp.linearCombination ℚ (fun v : OrderedSimplex K n =>
    if hv : StrictMono v.val then Finsupp.single (⟨v, hv⟩ : StrictOrderedSimplex K n) 1 else 0)

theorem strictChainProjection_single (K : Complex ι) (n : ℕ) (v : OrderedSimplex K n) :
    strictChainProjection K n (Finsupp.single v 1) =
      if hv : StrictMono v.val then Finsupp.single (⟨v, hv⟩ : StrictOrderedSimplex K n) 1 else 0 := by
  simp [strictChainProjection]

theorem strictChainProjection_boundary_single (K : Complex ι) (n : ℕ)
    (v : OrderedSimplex K (n + 1)) :
    strictChainProjection K n (weakRationalBoundary K n (Finsupp.single v 1)) =
      finiteRationalBoundary K n (strictChainProjection K (n + 1) (Finsupp.single v 1)) := by
  classical
  by_cases hv : StrictMono v.val
  · rw [strictChainProjection_single, dif_pos hv, finiteRationalBoundary_single,
      weakRationalBoundary_single]
    simp only [map_sum, map_zsmul, strictChainProjection_single]
    apply Finset.sum_congr rfl
    intro i _
    rw [dif_pos (orderedFace_strictMono K i v hv)]
    rfl
  · rw [strictChainProjection_single, dif_neg hv, map_zero, weakRationalBoundary_single]
    simp only [map_sum, map_zsmul]
    obtain ⟨i, hi⟩ := exists_adjacent_eq_of_not_strict v hv
    have hsum := Finset.sum_subset (s₁ := ({i.castSucc, i.succ} : Finset (Fin (n + 2))))
      (s₂ := Finset.univ) (Finset.subset_univ _) (f := fun j : Fin (n + 2) =>
        (-1 : ℤ) ^ (j : ℕ) • strictChainProjection K n (Finsupp.single (orderedFace K j v) 1))
      (by
        intro j _hj hj
        have hne : j ≠ i.castSucc ∧ j ≠ i.succ := by
          simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hj
        change (-1 : ℤ) ^ (j : ℕ) •
          strictChainProjection K n (Finsupp.single (orderedFace K j v) 1) = 0
        rw [strictChainProjection_single,
          dif_neg (not_strictMono_orderedFace_of_adjacent_eq v i hi j hne.1 hne.2), smul_zero])
    rw [← hsum, Finset.sum_pair (ne_of_lt (Fin.castSucc_lt_succ i)),
      orderedFace_eq_of_adjacent_eq v i hi]
    simp only [Fin.coe_castSucc, Fin.val_succ, pow_succ, mul_neg, mul_one,
      neg_smul, add_neg_cancel]

theorem strictChainProjection_boundary (K : Complex ι) (n : ℕ) :
    (strictChainProjection K n).comp (weakRationalBoundary K n) =
      (finiteRationalBoundary K n).comp (strictChainProjection K (n + 1)) := by
  apply Finsupp.lhom_ext
  intro v a
  have hsingle : Finsupp.single v a = a • Finsupp.single v 1 := by simp
  rw [hsingle]
  simp only [map_smul]
  congr 1
  exact strictChainProjection_boundary_single K n v

def strictChainInclusion (K : Complex ι) (n : ℕ) :
    FiniteRationalChains K n →ₗ[ℚ] WeakRationalChains K n :=
  Finsupp.lmapDomain ℚ ℚ (fun v : StrictOrderedSimplex K n => v.val)

theorem strictChainProjection_inclusion (K : Complex ι) (n : ℕ) :
    (strictChainProjection K n).comp (strictChainInclusion K n) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro v a
  have hsingle : Finsupp.single v a = a • Finsupp.single v 1 := by simp
  rw [hsingle]
  simp only [map_smul]
  congr 1
  simp only [LinearMap.comp_apply, strictChainInclusion, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, LinearMap.id_apply]
  rw [strictChainProjection_single, dif_pos v.property]
  rfl

end BanachIsometric.FiniteNerve
