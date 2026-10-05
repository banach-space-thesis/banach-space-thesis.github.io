import Posets.OrdinalClosedCoreCrossMassOperator
import Posets.OrdinalAmbientCoreBandsImage
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! Full-cardinality closed-core cross-mass selection for every infinite
index type. The proof uses an actual equivalence I x I = I and finite
mass-budget descent, retaining the original Cantor--Bendixson ranks. -/

noncomputable section
open Set Filter Topology
universe u v
namespace Posets
open ThesisCommon

variable {I K : Type*}

def wolfeIndexedCrossUnion (G : I → Set K) (i : I) : Set K := ⋃ j, ⋃ (_ : j ≠ i), G j

theorem mem_wolfeIndexedCrossUnion (G : I → Set K) (i : I) (x : K) :
    x ∈ wolfeIndexedCrossUnion G i ↔ ∃ j, j ≠ i ∧ x ∈ G j := by
  simp [wolfeIndexedCrossUnion]

theorem wolfeIndexedCrossUnion_reindex_subset (G : I → Set K) {J : Type*} {k : J → I}
    (hk : Function.Injective k) (i : J) :
    wolfeIndexedCrossUnion (G ∘ k) i ⊆ wolfeIndexedCrossUnion G (k i) := by
  intro x hx
  obtain ⟨j, hji, hj⟩ := (mem_wolfeIndexedCrossUnion _ _ _).mp hx
  exact (mem_wolfeIndexedCrossUnion _ _ _).mpr ⟨k j, hk.ne hji, hj⟩

theorem wolfeIndexedCrossUnion_isOpen [TopologicalSpace K] (G : I → Set K)
    (hG : ∀ i, IsOpen (G i)) (i : I) : IsOpen (wolfeIndexedCrossUnion G i) :=
  isOpen_iUnion fun j => isOpen_iUnion fun _ => hG j

def wolfeInfinitePairEquiv (I : Type v) [Infinite I] : I × I ≃ I :=
  Classical.choice (Cardinal.eq.mp (by
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mul_eq_self (Cardinal.aleph0_le_mk I)]))

theorem wolfeIndexedBool_subfamily [Infinite I] (colour : I → Bool) :
    ∃ (b : Bool) (k : I → I), Function.Injective k ∧ ∀ i, colour (k i) = b := by
  classical
  let A : Set I := {i | colour i = true}
  have hfull : ∃ b : Bool, Cardinal.mk {i : I | colour i = b} = Cardinal.mk I := by
    by_cases ha : Cardinal.mk I ≤ Cardinal.mk A
    · exact ⟨true, le_antisymm (Cardinal.mk_subtype_le A) ha⟩
    · have he : Aᶜ = {i : I | colour i = false} := by
        ext i
        cases h : colour i <;> simp [A, h]
      refine ⟨false, ?_⟩
      rw [← he]
      exact Cardinal.mk_compl_of_infinite A (lt_of_not_ge ha)
  obtain ⟨b, hb⟩ := hfull
  obtain ⟨e⟩ := Cardinal.eq.mp hb.symm
  exact ⟨b, fun i => (e i).val, Subtype.val_injective.comp e.injective,
    fun i => (e i).property⟩

theorem wolfeIndexedPairRow_injective (e : I × I ≃ I) (p : I) :
    Function.Injective (fun j => e (p, j)) := by
  intro i j h
  exact congrArg Prod.snd (e.injective h)

theorem wolfeIndexedPairDiagonal_injective (e : I × I ≃ I) (s : I → I) :
    Function.Injective (fun p => e (p, s p)) := by
  intro i j h
  exact congrArg Prod.fst (e.injective h)

theorem wolfeIndexedCrossUnion_pair_disjoint (e : I × I ≃ I) (G : I → Set K)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (s : I → I) (p : I) :
    Disjoint (wolfeIndexedCrossUnion (fun j => G (e (p, j))) (s p))
      (wolfeIndexedCrossUnion (fun r => G (e (r, s r))) p) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨j, _, hxj⟩ := (mem_wolfeIndexedCrossUnion _ _ _).mp hx
  obtain ⟨r, hrp, hyr⟩ := (mem_wolfeIndexedCrossUnion _ _ _).mp hy
  exact Set.disjoint_left.mp (hG (fun h => hrp (congrArg Prod.fst (e.injective h)).symm)) hxj hyr

variable {𝕜 : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem wolfeIndexedCrossUnion_pair_budget (M : JLMS.AtomicDualModel 𝕜 K)
    (e : I × I ≃ I) (G : I → Set K)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (s : I → I) (p : I)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {Q ε : ℝ}
    (hQ : wolfeMass M μ (wolfeIndexedCrossUnion G (e (p, s p))) ≤ Q)
    (hε : ε ≤ wolfeMass M μ (wolfeIndexedCrossUnion (fun j => G (e (p, j))) (s p))) :
    wolfeMass M μ (wolfeIndexedCrossUnion (fun r => G (e (r, s r))) p) ≤ Q - ε := by
  have hsub : wolfeIndexedCrossUnion (fun j => G (e (p, j))) (s p) ∪
      wolfeIndexedCrossUnion (fun r => G (e (r, s r))) p ⊆
      wolfeIndexedCrossUnion G (e (p, s p)) :=
    union_subset (wolfeIndexedCrossUnion_reindex_subset G (wolfeIndexedPairRow_injective e p) (s p))
      (wolfeIndexedCrossUnion_reindex_subset G (wolfeIndexedPairDiagonal_injective e s) p)
  have h := (wolfeMass_mono M μ hsub).trans hQ
  rw [wolfeMass_union M μ (wolfeIndexedCrossUnion_pair_disjoint e G hG s p)] at h
  linarith

variable {P : Type*} [TopologicalSpace P] [T1Space P]

def OrdinalIndexedCoreCrossMassSelection (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (L : I → Set P)
    (root : I → P) (γ : I → Ordinal.{u}) (G : I → Set K) (Q : ℝ) : Prop :=
  ∃ k : I → I, Function.Injective k ∧ ∃ L' : I → Set P,
    (∀ i, L' i ⊆ L (k i)) ∧
    (∀ i, root (k i) ∈ ordinalDerived (closure (L' i)) (γ (k i))) ∧
    ∀ i q, q ∈ L' i → wolfeMass M (v q) (wolfeIndexedCrossUnion (G ∘ k) i) ≤ Q

omit [T1Space P] in
theorem OrdinalIndexedCoreCrossMassSelection.comp (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (L : I → Set P)
    (root : I → P) (γ : I → Ordinal.{u}) (G : I → Set K)
    {k : I → I} (hk : Function.Injective k) (L' : I → Set P)
    (hL : ∀ i, L' i ⊆ L (k i)) {Q : ℝ}
    (hs : OrdinalIndexedCoreCrossMassSelection M v L' (root ∘ k) (γ ∘ k) (G ∘ k) Q) :
    OrdinalIndexedCoreCrossMassSelection M v L root γ G Q := by
  obtain ⟨j, hj, L'', hL'', hroot, hmass⟩ := hs
  exact ⟨k ∘ j, hk.comp hj, L'', fun i => (hL'' i).trans (hL (j i)), hroot, hmass⟩

theorem ordinalIndexedCoreCrossMass_selection_or_decrease (M : JLMS.AtomicDualModel 𝕜 K)
    (e : I × I ≃ I) (v : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (L : I → Set P)
    (root : I → P) (γ : I → Ordinal.{u}) (G : I → Set K)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hroot : ∀ i, root i ∈ ordinalDerived (closure (L i)) (γ i))
    {Q ε : ℝ}
    (hbudget : ∀ i q, q ∈ L i → wolfeMass M (v q) (wolfeIndexedCrossUnion G i) ≤ Q) :
    OrdinalIndexedCoreCrossMassSelection M v L root γ G ε ∨
      OrdinalIndexedCoreCrossMassSelection M v L root γ G (Q - ε) := by
  classical
  let S (r j : I) : Set P := {q |
    wolfeMass M (v q) (wolfeIndexedCrossUnion (fun n => G (e (r, n))) j) ≤ ε}
  by_cases hgood : ∃ r, ∀ j, root (e (r, j)) ∈
      ordinalDerived (closure (L (e (r, j)) ∩ S r j)) (γ (e (r, j)))
  · obtain ⟨r, hr⟩ := hgood
    left
    exact ⟨fun j => e (r, j), wolfeIndexedPairRow_injective e r,
      fun j => L (e (r, j)) ∩ S r j, fun _ => inter_subset_left,
      hr, fun _ _ hq => hq.2⟩
  · push_neg at hgood
    choose s hs using hgood
    let L' (r : I) : Set P := L (e (r, s r)) \ S r (s r)
    have hroot' (r : I) : root (e (r, s r)) ∈
        ordinalDerived (closure (L' r)) (γ (e (r, s r))) :=
      (ordinalDerived_closure_inter_or_diff (L (e (r, s r))) (S r (s r))
        (γ (e (r, s r))) (hroot (e (r, s r)))).resolve_left (hs r)
    right
    refine ⟨fun r => e (r, s r), wolfeIndexedPairDiagonal_injective e s, L',
      fun _ => diff_subset, hroot', ?_⟩
    intro r q hL
    apply wolfeIndexedCrossUnion_pair_budget M e G hG s r (v q) (hbudget _ q hL.1)
    exact le_of_lt (lt_of_not_ge hL.2)

variable [Infinite I]

theorem ordinalIndexedCoreCrossMass_exists_of_budget (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (L : I → Set P)
    (root : I → P) (γ : I → Ordinal.{u}) (G : I → Set K)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hroot : ∀ i, root i ∈ ordinalDerived (closure (L i)) (γ i))
    {Q ε : ℝ} (hε : 0 < ε)
    (hbudget : ∀ i q, q ∈ L i → wolfeMass M (v q) (wolfeIndexedCrossUnion G i) ≤ Q) :
    OrdinalIndexedCoreCrossMassSelection M v L root γ G ε := by
  classical
  by_contra hfail
  have hdesc (n : ℕ) : OrdinalIndexedCoreCrossMassSelection M v L root γ G (Q - n * ε) := by
    induction n with
    | zero =>
        refine ⟨id, Function.injective_id, L, fun _ => Subset.rfl, hroot, ?_⟩
        simpa using hbudget
    | succ n ih =>
        obtain ⟨k, hk, L', hL', hr, hb⟩ := ih
        have hG' : Pairwise (fun i j => Disjoint ((G ∘ k) i) ((G ∘ k) j)) :=
          fun _ _ hij => hG (hk.ne hij)
        rcases ordinalIndexedCoreCrossMass_selection_or_decrease M (wolfeInfinitePairEquiv I)
            v L' (root ∘ k) (γ ∘ k) (G ∘ k) hG' hr hb with hs | hs
        · exact (hfail (OrdinalIndexedCoreCrossMassSelection.comp M v L root γ G hk L' hL' hs)).elim
        · have h := OrdinalIndexedCoreCrossMassSelection.comp M v L root γ G hk L' hL' hs
          convert h using 1
          push_cast
          ring
  obtain ⟨N, hN⟩ := exists_nat_gt (Q / ε)
  have hN' : Q < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  obtain ⟨k, _, L', _, hr, hb⟩ := hdesc N
  let i₀ : I := Classical.choice (inferInstance : Nonempty I)
  have hp : root (k i₀) ∈ closure (L' i₀) := by
    simpa only [ordinalDerived_zero] using
      ordinalDerived_antitone isClosed_closure (Ordinal.zero_le (γ (k i₀))) (hr i₀)
  have hne : (L' i₀).Nonempty := by
    by_contra h
    have he : L' i₀ = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp only [he, closure_empty, mem_empty_iff_false] at hp
  obtain ⟨q, hq⟩ := hne
  have hu := hb i₀ q hq
  have hl := wolfeMass_nonneg M (v q) (wolfeIndexedCrossUnion (G ∘ k) i₀)
  linarith

theorem ordinalIndexedCore_exists_crossMass_leaves (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (L : I → Set P)
    (root : I → P) (γ : I → Ordinal.{u}) (G : I → Set K)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hroot : ∀ i, root i ∈ ordinalDerived (closure (L i)) (γ i))
    {Q : ℝ} (hnorm : ∀ i q, q ∈ L i → ‖WeakDual.toStrongDual (v q)‖ ≤ Q)
    {ε : ℝ} (hε : 0 < ε) :
    OrdinalIndexedCoreCrossMassSelection M v L root γ G ε :=
  ordinalIndexedCoreCrossMass_exists_of_budget M v L root γ G hG hroot hε
    (fun i q hq => (wolfeMass_le_norm M (v q) _).trans (hnorm i q hq))

variable [LocallyCompactSpace K] [T2Space K]

theorem ordinalIndexedCore_exists_crossMass_closure (M : JLMS.AtomicDualModel 𝕜 K)
    (hK : JLMS.IsScattered K) (v : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hv : Continuous v)
    (L : I → Set P) (root : I → P) (γ : I → Ordinal.{u}) (G : I → Set K)
    (hGopen : ∀ i, IsOpen (G i)) (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hroot : ∀ i, root i ∈ ordinalDerived (closure (L i)) (γ i))
    {Q : ℝ} (hnorm : ∀ i q, q ∈ L i → ‖WeakDual.toStrongDual (v q)‖ ≤ Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : I → I, Function.Injective k ∧ ∃ L' : I → Set P,
      (∀ i, L' i ⊆ L (k i)) ∧
      (∀ i, root (k i) ∈ ordinalDerived (closure (L' i)) (γ (k i))) ∧
      ∀ i q, q ∈ closure (L' i) →
        wolfeMass M (v q) (wolfeIndexedCrossUnion (G ∘ k) i) < ε := by
  obtain ⟨k, hk, L', hL', hr, hb⟩ := ordinalIndexedCore_exists_crossMass_leaves
    M v L root γ G hG hroot hnorm (half_pos hε)
  refine ⟨k, hk, L', hL', hr, ?_⟩
  intro i q hq
  have hclosed : IsClosed {μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K) |
      wolfeMass M μ (wolfeIndexedCrossUnion (G ∘ k) i) ≤ ε / 2} := by
    simpa only [Set.compl_setOf, not_lt] using
      (isOpen_wolfeMass_gt M hK
        (wolfeIndexedCrossUnion_isOpen _ (fun j => hGopen _) i) (ε / 2)).isClosed_compl
  have hle : wolfeMass M (v q) (wolfeIndexedCrossUnion (G ∘ k) i) ≤ ε / 2 :=
    closure_minimal (fun x hx => hb i x hx) (hclosed.preimage hv) hq
  exact hle.trans_lt (half_lt_self hε)

theorem ordinalIndexedCore_operator_crossMass (M : JLMS.AtomicDualModel 𝕜 K)
    (hK : JLMS.IsScattered K) (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (L G : I → Set K) (root : I → K) (γ : I → Ordinal.{u})
    (hGopen : ∀ i, IsOpen (G i)) (hGcompact : ∀ i, IsCompact (G i))
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (hL : ∀ i, L i ⊆ G i)
    (hroot : ∀ i, root i ∈ ordinalDerived (closure (L i)) (γ i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : I → I, Function.Injective k ∧ ∃ C : I → Set K,
      (∀ i, IsCompact (C i)) ∧ (∀ i, C i ⊆ closure (L (k i))) ∧
      (∀ i, C i ⊆ G (k i)) ∧
      (∀ i, root (k i) ∈ ordinalDerived (C i) (γ (k i))) ∧
      ∀ i x, x ∈ C i → wolfeMass M (wolfeOperatorRow T x)
        (wolfeIndexedCrossUnion (G ∘ k) i) < ε := by
  obtain ⟨k, hk, L', hL', hr, hm⟩ := ordinalIndexedCore_exists_crossMass_closure
    M hK (wolfeOperatorRow T) (wolfeOperatorRow_continuous T) L root γ G hGopen hG hroot
    (Q := ‖T‖) (fun _ x _ => wolfeOperatorRow_norm_le T x) hε
  have hsub (i : I) : closure (L' i) ⊆ G (k i) :=
    closure_minimal ((hL' i).trans (hL (k i))) (hGcompact (k i)).isClosed
  exact ⟨k, hk, fun i => closure (L' i),
    fun i => (hGcompact (k i)).of_isClosed_subset isClosed_closure (hsub i),
    fun i => closure_mono (hL' i), hsub, hr, hm⟩

theorem ordinalAmbientCore_infinite_crossMass
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    (θ γ : I → Ordinal.{u}) (hθ : ∀ i, θ i ∈ ordinalTowerLevel (θ i) (γ i))
    (e : ∀ i, Iic (θ i) → K) (he : ∀ i, IsOpenEmbedding (e i))
    (hdisj : Pairwise (fun i j => Disjoint (range (e i)) (range (e j))))
    (a : ∀ i, ℕ → Iic (γ i)) (ha : ∀ i, Monotone (a i))
    {N : ℕ} {ε δ : ℝ} (hN : ‖T‖ + ‖S‖ < N * ε) (hδ : 0 < δ)
    (ρ : I → Ordinal.{v}) (x : ∀ i, Iic (θ i))
    (hx : ∀ i, x i ∈ ordinalDerived (univ : Set (Iic (θ i))) (ρ i)) :
    ∃ (b : Bool) (k : I → I), Function.Injective k ∧
      ∃ (n : I → Fin N) (C : I → Set K),
        (∀ i, IsCompact (C i)) ∧
        (∀ i, C i ⊆ closure (e (k i) ''
          ordinalAmbientBandLeaves (hθ (k i)) (e (k i)) (he (k i)) M T S
            (a (k i)) (n i).val b ε)) ∧
        (∀ i, C i ⊆ range (e (k i))) ∧
        (∀ i, e (k i) (x (k i)) ∈ ordinalDerived (C i) (ρ (k i))) ∧
        ∀ i y, y ∈ C i → wolfeMass M (wolfeOperatorRow (if b then T else S) y)
          (wolfeIndexedCrossUnion (fun j => range (e (k j))) i) < δ := by
  classical
  have hex (i : I) := ordinalAmbientCore_exists_coloured_image (hθ i) (e i) (he i)
    M T S hTS (a i) (ha i) hN (ρ i) (hx i)
  choose colour hc using hex
  obtain ⟨b, k₁, hk₁, hb⟩ := wolfeIndexedBool_subfamily (fun i => (colour i).2)
  let L : I → Set K := fun i => e (k₁ i) ''
    ordinalAmbientBandLeaves (hθ (k₁ i)) (e (k₁ i)) (he (k₁ i)) M T S
      (a (k₁ i)) (colour (k₁ i)).1.val b ε
  let G : I → Set K := fun i => range (e (k₁ i))
  have hGo (i : I) : IsOpen (G i) := (he (k₁ i)).isOpen_range
  have hGc (i : I) : IsCompact (G i) := by
    letI : CompactSpace (Iic (θ (k₁ i))) :=
      isCompact_iff_compactSpace.mp (ordinalClosedCore_interval_compact _)
    exact isCompact_range (he (k₁ i)).continuous
  have hGd : Pairwise (fun i j => Disjoint (G i) (G j)) := by
    intro i j hij
    exact hdisj (fun h => hij (hk₁ h))
  have hL (i : I) : L i ⊆ G i := image_subset_range _ _
  have hr (i : I) : e (k₁ i) (x (k₁ i)) ∈ ordinalDerived (closure (L i)) (ρ (k₁ i)) := by
    have hr' := (hc (k₁ i)).2.2
    simpa only [L, hb i] using hr'
  obtain ⟨k₂, hk₂, C, hCc, hCL, hCG, hCr, hCm⟩ := ordinalIndexedCore_operator_crossMass M hK
    (if b then T else S) L G (fun i => e (k₁ i) (x (k₁ i))) (ρ ∘ k₁)
    hGo hGc hGd hL hr hδ
  exact ⟨b, k₁ ∘ k₂, hk₁.comp hk₂, fun i => (colour (k₁ (k₂ i))).1, C,
    hCc, hCL, hCG, hCr, hCm⟩

end Posets

