import Sigma.ComplexConstructionState

/-! A good partial construction extends by one genuine pair of splittings. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

theorem exists_goodComplexConstruction_insert {I : Type} [DecidableEq I]
    {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (ρ σ : I → ℕ → ComplexPairedMeasure) (d : ComplexConstructionData μ μtilde R Rtilde)
    (V : Set I) (a : I) (ha : a ∉ V) (hV : #V < 𝔠)
    (hgood : GoodComplexConstruction ρ σ d V)
    (hR : (R a).Infinite) (hRt : (Rtilde a).Infinite)
    (hμ : ComplexAdmissible (μ a)) (hμt : ComplexAdmissible (μtilde a)) :
    ∃ x : ComplexThreeLevelChoice (μ a) (R a) × ComplexThreeLevelChoice (μtilde a) (Rtilde a),
      GoodComplexConstruction ρ σ (Function.update d a x) (insert a V) := by
  classical
  let κ : Cardinal := max #V ℵ₀
  have hκ : ℵ₀ ≤ κ := le_max_right _ _
  have hκlt : κ < 𝔠 := max_lt hV Cardinal.aleph0_lt_continuum
  have hVκ : #V ≤ κ := le_max_left _ _
  have hremκ (i : I) : #(V \ {i} : Set I) ≤ κ := (Cardinal.mk_le_mk_of_subset Set.diff_subset).trans hVκ
  let J := (V × Bool) ⊕ (V × Bool)
  let L : J → BooleanSubalgebra (Set ℕ) := Sum.elim
    (fun p => complexConstructionAlgebra d false (V \ {p.1.val}))
    (fun _ => complexConstructionAlgebra d false V)
  let T : J → BooleanSubalgebra (Set ℕ) := Sum.elim
    (fun _ => complexConstructionAlgebra d true V)
    (fun p => complexConstructionAlgebra d true (V \ {p.1.val}))
  let M : J → Set ComplexPairedMeasure := Sum.elim
    (fun p => ρ p.1.val '' (d p.1.val).1.cutLeft p.2)
    (fun p => σ p.1.val '' (d p.1.val).2.cutLeft p.2)
  let N : J → Set ComplexPairedMeasure := Sum.elim
    (fun p => ρ p.1.val '' (d p.1.val).1.cutRight p.2)
    (fun p => σ p.1.val '' (d p.1.val).2.cutRight p.2)
  have hn (j : J) : ¬ ComplexPairedSeparated (L j) (T j) (M j) (N j) := by
    cases j with
    | inl p => exact ((d p.1.val).1.pairedNonseparated_iff_cuts _ _ _).mp (hgood _ p.1.property).1 p.2
    | inr p => exact ((d p.1.val).2.pairedNonseparated_iff_cuts _ _ _).mp (hgood _ p.1.property).2 p.2
  have hL (j : J) : #(L j) ≤ κ := by
    cases j with
    | inl p => exact complexConstructionAlgebra_cardinal_le d false _ κ hκ (hremκ p.1.val)
    | inr p => exact complexConstructionAlgebra_cardinal_le d false _ κ hκ hVκ
  have hT (j : J) : #(T j) ≤ κ := by
    cases j with
    | inl p => exact complexConstructionAlgebra_cardinal_le d true _ κ hκ hVκ
    | inr p => exact complexConstructionAlgebra_cardinal_le d true _ κ hκ (hremκ p.1.val)
  have hLf (j : J) (A : Set ℕ) (hA : A.Finite) : A ∈ L j := by
    cases j <;> exact complexConstructionAlgebra_finite_mem d false _ hA
  have hTf (j : J) (A : Set ℕ) (hA : A.Finite) : A ∈ T j := by
    cases j <;> exact complexConstructionAlgebra_finite_mem d true _ hA
  have hJ : #J ≤ κ := by
    have hp : #(V × Bool) ≤ κ := by
      simpa only [Cardinal.mk_prod, Cardinal.lift_id] using
        (mul_le_mul' hVκ (Cardinal.mk_le_aleph0.trans hκ : #Bool ≤ κ)).trans_eq
          (Cardinal.mul_eq_self hκ)
    simpa only [J, Cardinal.mk_sum, Cardinal.lift_id] using
      (add_le_add hp hp).trans_eq (Cardinal.add_eq_self hκ)
  obtain ⟨x,xt,hnew,hnewt,hpres⟩ := complex_exists_twoSided_successor L T κ hκ hκlt hJ hL hT hLf hTf
    M N hn (R a) (Rtilde a) hR hRt (μ a) (μtilde a) hμ hμt (ρ a) (σ a)
    (complexConstructionAlgebra d false V) (complexConstructionAlgebra d true V)
    (complexConstructionAlgebra_cardinal_le d false V κ hκ hVκ)
    (complexConstructionAlgebra_cardinal_le d true V κ hκ hVκ)
    (fun A hA => complexConstructionAlgebra_finite_mem d true V hA)
  let e : ComplexConstructionData μ μtilde R Rtilde := Function.update d a (x,xt)
  have hea : e a = (x,xt) := Function.update_self a (x,xt) d
  have heold (i : I) (hi : i ∈ V) : e i = d i :=
    Function.update_of_ne (show i ≠ a from fun h => ha (h ▸ hi)) _ _
  have healg (s : Bool) (W : Set I) (hW : W ⊆ V) :
      complexConstructionAlgebra e s W = complexConstructionAlgebra d s W :=
    complexConstructionAlgebra_congr e d s W (fun i hi => heold i (hW hi))
  have hleft (W : Set I) (hW : W ⊆ V) : complexConstructionAlgebra e false (insert a W) =
      x.adjoin (complexConstructionAlgebra d false W) := by
    rw [complexConstructionAlgebra_insert_left, hea, healg false W hW]
  have hright (W : Set I) (hW : W ⊆ V) : complexConstructionAlgebra e true (insert a W) =
      xt.adjoin (complexConstructionAlgebra d true W) := by
    rw [complexConstructionAlgebra_insert_right, hea, healg true W hW]
  refine ⟨(x,xt), ?_⟩
  change GoodComplexConstruction ρ σ e (insert a V)
  intro i hi
  rcases hi with rfl | hi
  · have hremove : insert i V \ {i} = V := by
      ext j
      simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h, hne⟩
        exact h.resolve_left hne
      · intro hj
        exact ⟨Or.inr hj, fun h => ha (h ▸ hj)⟩
    rw [hea, hremove, healg false V Set.Subset.rfl, healg true V Set.Subset.rfl,
      hleft V Set.Subset.rfl, hright V Set.Subset.rfl]
    exact ⟨hnew,hnewt⟩
  · have hia : i ≠ a := fun h => ha (h ▸ hi)
    have hremove : insert a V \ {i} = insert a (V \ {i}) := by
      ext j
      simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h, hne⟩
        rcases h with rfl | h
        · exact Or.inl rfl
        · exact Or.inr ⟨h,hne⟩
      · rintro (rfl | ⟨h,hne⟩)
        · exact ⟨Or.inl rfl, Ne.symm hia⟩
        · exact ⟨Or.inr h,hne⟩
    rw [heold i hi, hremove, hleft _ Set.diff_subset, hright _ Set.diff_subset,
      hleft V Set.Subset.rfl, hright V Set.Subset.rfl]
    constructor
    · apply ((d i).1.pairedNonseparated_iff_cuts _ _ _).mpr
      intro b
      exact hpres (.inl (⟨i,hi⟩,b))
    · apply ((d i).2.pairedNonseparated_iff_cuts _ _ _).mpr
      intro b
      exact hpres (.inr (⟨i,hi⟩,b))

end SigmaNonprimarity
