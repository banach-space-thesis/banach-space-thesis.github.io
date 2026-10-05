import ThesisCommon.Analysis.GowersMaureyOrbitWitnesses

/-! Simultaneous gliding-hump selection of genuine finite dual witnesses.
The operator's two off-diagonal directions are controlled by any prescribed
positive product weights. Cross terms for the already reached finite spread
orbits vanish exactly, while the original operator acts on its actual subspace. -/
noncomputable section
open Filter
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem pairing_eq_zero_of_before {a x : C00 𝕜} (h : Before a x) : pairing a x = 0 := by
  classical
  simp only [pairing, Finsupp.lsum_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro i hi
  have ha : a i = 0 := Finsupp.notMem_support_iff.mp (fun hai => (h i hai i hi).false)
  simp [ha]

theorem pairing_eq_zero_of_before_rev {a x : C00 𝕜} (h : Before x a) : pairing a x = 0 := by
  classical
  simp only [pairing, Finsupp.lsum_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro i hi
  have ha : a i = 0 := Finsupp.notMem_support_iff.mp (fun hai => (h i hi i hai).false)
  simp [ha]

structure SeparatedOrbitWitnessSequence {D : ConstructionData 𝕜}
    {Y : Submodule 𝕜 (ShiftSpace D)} (u : BlockTestSequence D Y)
    (T : Y →L[𝕜] ShiftSpace D) (ε : ℝ) (weight : ℕ → ℝ) where
  rank : ℕ → ℕ
  index : ℕ → ℕ
  functional : ℕ → C00 𝕜
  rank_pos : ∀ i, 0 < rank i
  rank_strict : StrictMono rank
  index_strict : StrictMono index
  successive : ∀ i j, i < j → Before (functional i) (functional j)
  dualUnit : ∀ i, DualUnit (implicitNorm D) (functional i)
  nonzero : ∀ i, functional i ≠ 0
  detected : ∀ i, ε/4 < RCLike.re
    (completedPairing D (functional i) (T (u.inSubspace (index i))))
  orbit_small : ∀ i, ∀ z ∈ spreadParameterSquare (rank i),
    ‖pairing (functional i) (spread z.1 z.2 (u.vector (index i)))‖ ≤ ‖T‖ / rank i
  cross_image : ∀ i j, i < j →
    ‖completedPairing D (functional i) (T (u.inSubspace (index j)))‖ <
        weight (rank i) * weight (rank j) ∧
    ‖completedPairing D (functional j) (T (u.inSubspace (index i)))‖ <
        weight (rank i) * weight (rank j)
  cross_spread : ∀ i j, i < j → ∀ z ∈ spreadParameterSquare (rank i),
    pairing (functional i) (spread z.1 z.2 (u.vector (index j))) = 0 ∧
    pairing (functional j) (spread z.1 z.2 (u.vector (index i))) = 0

theorem exists_separated_orbit_witness_sequence
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) (hne : ∀ i, u.vector i ≠ 0)
    (T : Y →L[𝕜] ShiftSpace D) (q : ℕ → ℕ) (hq : StrictMono q)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ i, ∀ z ∈ spreadVectorOrbit D (u.vector i) (q i),
      ε ≤ ‖T (u.inSubspace i)-z‖)
    (weight : ℕ → ℝ) (hweight : ∀ i, 0 < weight i) :
    Nonempty (SeparatedOrbitWitnessSequence u T ε weight) := by
  classical
  let A := ℕ × ℕ × C00 𝕜
  let P (a : A) := 0 < a.1 ∧ DualUnit (implicitNorm D) a.2.2 ∧ a.2.2 ≠ 0 ∧
    ε/4 < RCLike.re (completedPairing D a.2.2 (T (u.inSubspace a.2.1))) ∧
    ∀ z ∈ spreadParameterSquare a.1,
      ‖pairing a.2.2 (spread z.1 z.2 (u.vector a.2.1))‖ ≤ ‖T‖ / a.1
  let R (a b : A) := a.1 < b.1 ∧ a.2.1 < b.2.1 ∧ Before a.2.2 b.2.2 ∧
    (‖completedPairing D a.2.2 (T (u.inSubspace b.2.1))‖ < weight a.1 * weight b.1 ∧
     ‖completedPairing D b.2.2 (T (u.inSubspace a.2.1))‖ < weight a.1 * weight b.1) ∧
    ∀ z ∈ spreadParameterSquare a.1,
      pairing a.2.2 (spread z.1 z.2 (u.vector b.2.1)) = 0 ∧
      pairing b.2.2 (spread z.1 z.2 (u.vector a.2.1)) = 0
  have hselect : ∀ s : Finset A, (∀ a ∈ s, P a) → ∃ b, P b ∧ ∀ a ∈ s, R a b := by
    intro s _
    let r := s.sup Prod.fst + 1
    let K0 := s.sup (fun a => max (a.2.2.support.sup id)
      ((spreadParameterSquare a.1).sup
        (fun z => (spread z.1 z.2 (u.vector a.2.1)).support.sup id)))
    have htail : ∀ᶠ K : ℕ in atTop, K0 ≤ K ∧ ∀ a ∈ s, ∀ b : C00 𝕜,
        b ∈ afterCutoff K → DualUnit (implicitNorm D) b →
          ‖completedPairing D b (T (u.inSubspace a.2.1))‖ < weight a.1 * weight r := by
      apply Eventually.and (eventually_ge_atTop K0)
      apply (eventually_all_finset s).mpr
      intro a _
      exact eventually_tail_dualUnit_small D _ (mul_pos (hweight _) (hweight _))
    obtain ⟨K,hK,htailK⟩ := htail.exists
    have hfront : ∀ᶠ i : ℕ in atTop, ∀ a ∈ s,
        ‖completedPairing D a.2.2 (T (u.inSubspace i))‖ < weight a.1 * weight r := by
      apply (eventually_all_finset s).mpr
      intro a _
      have h := u.tendsto_subspace_functional_zero ((completedPairing D a.2.2).comp T)
      exact h.norm.eventually_lt_const (by simpa using mul_pos (hweight a.1) (hweight r))
    have hevent := ((u.eventually_finite_orbit_witnesses hne T q hq hε hsep r K
      (Nat.succ_pos _)).and hfront).and (eventually_gt_atTop (s.sup (fun a => a.2.1)))
    obtain ⟨i,⟨⟨himages,b,hbK,hbu,hb0,hbdet,hborbit⟩,hfronti⟩,hi⟩ := hevent.exists
    refine ⟨(r,i,b),⟨Nat.succ_pos _,hbu,hb0,hbdet,hborbit⟩,?_⟩
    intro a ha
    have har : a.1 < r := (Finset.le_sup (f := Prod.fst) ha).trans_lt (Nat.lt_succ_self _)
    have haK : ∀ j ∈ a.2.2.support, j ≤ K := by
      intro j hj
      exact (Finset.le_sup (f := id) hj).trans ((le_max_left _ _).trans
        ((Finset.le_sup (f := fun a : A => max (a.2.2.support.sup id)
          ((spreadParameterSquare a.1).sup
            (fun z => (spread z.1 z.2 (u.vector a.2.1)).support.sup id))) ha).trans hK))
    refine ⟨har,(Finset.le_sup (f := fun a : A => a.2.1) ha).trans_lt hi,
      before_of_mem_afterCutoff haK hbK,⟨hfronti a ha,htailK a ha b hbK hbu⟩,?_⟩
    intro z hz
    refine ⟨pairing_eq_zero_of_before (before_of_mem_afterCutoff haK
      (himages z (spreadParameterSquare_mono har.le hz))),?_⟩
    apply pairing_eq_zero_of_before_rev
    apply before_of_mem_afterCutoff (K := K) _ hbK
    intro j hj
    exact (Finset.le_sup (f := id) hj).trans ((Finset.le_sup
      (f := fun z : ℕ × ℕ => (spread z.1 z.2 (u.vector a.2.1)).support.sup id) hz).trans
      ((le_max_right _ _).trans ((Finset.le_sup (f := fun a : A => max (a.2.2.support.sup id)
        ((spreadParameterSquare a.1).sup
          (fun z => (spread z.1 z.2 (u.vector a.2.1)).support.sup id))) ha).trans hK)))
  obtain ⟨w,hw,hwr⟩ := exists_seq_of_forall_finset_exists P R hselect
  exact ⟨{
    rank := fun i => (w i).1
    index := fun i => (w i).2.1
    functional := fun i => (w i).2.2
    rank_pos := fun i => (hw i).1
    rank_strict := fun i j hij => (hwr i j hij).1
    index_strict := fun i j hij => (hwr i j hij).2.1
    successive := fun i j hij => (hwr i j hij).2.2.1
    dualUnit := fun i => (hw i).2.1
    nonzero := fun i => (hw i).2.2.1
    detected := fun i => (hw i).2.2.2.1
    orbit_small := fun i => (hw i).2.2.2.2
    cross_image := fun i j hij => (hwr i j hij).2.2.2.1
    cross_spread := fun i j hij => (hwr i j hij).2.2.2.2
  }⟩

end ThesisCommon.GowersMaurey
