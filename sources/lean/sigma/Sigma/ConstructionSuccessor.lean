import Sigma.ConstructionState

/-! A good partial construction extends by one genuine pair of splittings. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

theorem exists_goodConstruction_insert {I : Type} [DecidableEq I]
    {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (ρ σ : I → ℕ → PairedMeasure) (d : ConstructionData μ μtilde R Rtilde)
    (V : Set I) (a : I) (ha : a ∉ V) (hV : #V < 𝔠)
    (hgood : GoodConstruction ρ σ d V)
    (hR : (R a).Infinite) (hRt : (Rtilde a).Infinite)
    (hμ : Admissible (μ a)) (hμt : Admissible (μtilde a)) :
    ∃ x : ThreeLevelChoice (μ a) (R a) × ThreeLevelChoice (μtilde a) (Rtilde a),
      GoodConstruction ρ σ (Function.update d a x) (insert a V) := by
  classical
  let κ : Cardinal := max #V ℵ₀
  have hκ : ℵ₀ ≤ κ := le_max_right _ _
  have hκlt : κ < 𝔠 := max_lt hV Cardinal.aleph0_lt_continuum
  have hVκ : #V ≤ κ := le_max_left _ _
  have hremκ (i : I) : #(V \ {i} : Set I) ≤ κ := (Cardinal.mk_le_mk_of_subset Set.diff_subset).trans hVκ
  let J := (V × Bool) ⊕ (V × Bool)
  let L : J → BooleanSubalgebra (Set ℕ) := Sum.elim
    (fun p => constructionAlgebra d false (V \ {p.1.val}))
    (fun _ => constructionAlgebra d false V)
  let T : J → BooleanSubalgebra (Set ℕ) := Sum.elim
    (fun _ => constructionAlgebra d true V)
    (fun p => constructionAlgebra d true (V \ {p.1.val}))
  let M : J → Set PairedMeasure := Sum.elim
    (fun p => ρ p.1.val '' (d p.1.val).1.cutLeft p.2)
    (fun p => σ p.1.val '' (d p.1.val).2.cutLeft p.2)
  let N : J → Set PairedMeasure := Sum.elim
    (fun p => ρ p.1.val '' (d p.1.val).1.cutRight p.2)
    (fun p => σ p.1.val '' (d p.1.val).2.cutRight p.2)
  have hn (j : J) : ¬ PairedSeparated (L j) (T j) (M j) (N j) := by
    cases j with
    | inl p => exact ((d p.1.val).1.nonseparated_iff_cuts _ _ _).mp (hgood _ p.1.property).1 p.2
    | inr p => exact ((d p.1.val).2.nonseparated_iff_cuts _ _ _).mp (hgood _ p.1.property).2 p.2
  have hL (j : J) : #(L j) ≤ κ := by
    cases j with
    | inl p => exact constructionAlgebra_cardinal_le d false _ κ hκ (hremκ p.1.val)
    | inr p => exact constructionAlgebra_cardinal_le d false _ κ hκ hVκ
  have hT (j : J) : #(T j) ≤ κ := by
    cases j with
    | inl p => exact constructionAlgebra_cardinal_le d true _ κ hκ hVκ
    | inr p => exact constructionAlgebra_cardinal_le d true _ κ hκ (hremκ p.1.val)
  have hLf (j : J) (A : Set ℕ) (hA : A.Finite) : A ∈ L j := by
    cases j <;> exact constructionAlgebra_finite_mem d false _ hA
  have hTf (j : J) (A : Set ℕ) (hA : A.Finite) : A ∈ T j := by
    cases j <;> exact constructionAlgebra_finite_mem d true _ hA
  have hJ : #J ≤ κ := by
    have hp : #(V × Bool) ≤ κ := by
      simpa only [Cardinal.mk_prod, Cardinal.lift_id] using
        (mul_le_mul' hVκ (Cardinal.mk_le_aleph0.trans hκ : #Bool ≤ κ)).trans_eq
          (Cardinal.mul_eq_self hκ)
    simpa only [J, Cardinal.mk_sum, Cardinal.lift_id] using
      (add_le_add hp hp).trans_eq (Cardinal.add_eq_self hκ)
  obtain ⟨x,xt,hnew,hnewt,hpres⟩ := exists_twoSided_successor L T κ hκ hκlt hJ hL hT hLf hTf
    M N hn (R a) (Rtilde a) hR hRt (μ a) (μtilde a) hμ hμt (ρ a) (σ a)
    (constructionAlgebra d false V) (constructionAlgebra d true V)
    (constructionAlgebra_cardinal_le d false V κ hκ hVκ)
    (constructionAlgebra_cardinal_le d true V κ hκ hVκ)
    (fun A hA => constructionAlgebra_finite_mem d true V hA)
  let e : ConstructionData μ μtilde R Rtilde := Function.update d a (x,xt)
  have hea : e a = (x,xt) := Function.update_self a (x,xt) d
  have heold (i : I) (hi : i ∈ V) : e i = d i :=
    Function.update_of_ne (show i ≠ a from fun h => ha (h ▸ hi)) _ _
  have healg (s : Bool) (W : Set I) (hW : W ⊆ V) :
      constructionAlgebra e s W = constructionAlgebra d s W :=
    constructionAlgebra_congr e d s W (fun i hi => heold i (hW hi))
  have hleft (W : Set I) (hW : W ⊆ V) : constructionAlgebra e false (insert a W) =
      x.adjoin (constructionAlgebra d false W) := by
    rw [constructionAlgebra_insert_left, hea, healg false W hW]
  have hright (W : Set I) (hW : W ⊆ V) : constructionAlgebra e true (insert a W) =
      xt.adjoin (constructionAlgebra d true W) := by
    rw [constructionAlgebra_insert_right, hea, healg true W hW]
  refine ⟨(x,xt), ?_⟩
  change GoodConstruction ρ σ e (insert a V)
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
    · apply ((d i).1.nonseparated_iff_cuts _ _ _).mpr
      intro b
      exact hpres (.inl (⟨i,hi⟩,b))
    · apply ((d i).2.nonseparated_iff_cuts _ _ _).mpr
      intro b
      exact hpres (.inr (⟨i,hi⟩,b))

end SigmaNonprimarity
