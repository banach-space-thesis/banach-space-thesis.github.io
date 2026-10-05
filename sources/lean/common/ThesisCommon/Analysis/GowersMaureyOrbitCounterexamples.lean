import ThesisCommon.Analysis.FiniteParameterOrbits
import ThesisCommon.Analysis.GowersMaureySpreadExhaustion
import ThesisCommon.Analysis.GowersMaureyBlockImageTails

/-! Failure of the source's vectorwise finite-orbit approximation supplies an
actual successive block test sequence. The original growing parameter, tail
condition, and separation from the entire coefficient-budget orbit are kept. -/
noncomputable section
open Filter
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def spreadVectorOrbit (D : ConstructionData 𝕜) (x : C00 𝕜) (r : ℕ) : Set (ShiftSpace D) :=
  finiteParameterOrbit (𝕜 := 𝕜)
    (fun z : ℕ × ℕ => denseEmbedding D (spread z.1 z.2 x)) (spreadParameterSquare r) r

theorem spreadVectorOrbit_mono (D : ConstructionData 𝕜) (x : C00 𝕜) :
    Monotone (spreadVectorOrbit D x) := by
  intro r s hrs
  exact finiteParameterOrbit_mono _ (spreadParameterSquare_mono hrs) (by exact_mod_cast hrs)

theorem zero_mem_spreadVectorOrbit (D : ConstructionData 𝕜) (x : C00 𝕜) (r : ℕ) :
    (0 : ShiftSpace D) ∈ spreadVectorOrbit D x r :=
  zero_mem_finiteParameterOrbit _ _ (Nat.cast_nonneg r)

theorem exists_block_orbit_counterexamples (D : ConstructionData 𝕜)
    (Y : Submodule 𝕜 (ShiftSpace D)) (T : Y →L[𝕜] ShiftSpace D)
    {ε : ℝ} (hε : 0 < ε)
    (hbad : ∀ r : ℕ, 0 < r → ∃ x : C00 𝕜, ∃ hx : denseEmbedding D x ∈ Y,
      intervalNorm D r x ≤ 1 ∧ x ∈ afterCutoff r ∧
      ∀ z ∈ spreadVectorOrbit D x r, ε ≤ ‖T ⟨denseEmbedding D x,hx⟩ - z‖) :
    ∃ u : BlockTestSequence D Y, ∃ q : ℕ → ℕ, StrictMono q ∧
      (∀ i, i+1 ≤ q i) ∧ (∀ i, u.vector i ≠ 0) ∧
      (∀ i, u.vector i ∈ afterCutoff (q i)) ∧
      ∀ i, ∀ z ∈ spreadVectorOrbit D (u.vector i) (q i),
        ε ≤ ‖T (u.inSubspace i)-z‖ := by
  classical
  let A := {x : C00 𝕜 // denseEmbedding D x ∈ Y}
  let P (a : ℕ × A) := 0 < a.1 ∧ intervalNorm D a.1 a.2.1 ≤ 1 ∧
    a.2.1 ∈ afterCutoff a.1 ∧ ∀ z ∈ spreadVectorOrbit D a.2.1 a.1,
      ε ≤ ‖T ⟨denseEmbedding D a.2.1,a.2.2⟩-z‖
  let R (a b : ℕ × A) := a.1 < b.1 ∧ Before a.2.1 b.2.1
  have hs : ∀ s : Finset (ℕ × A), (∀ a ∈ s, P a) → ∃ b, P b ∧ ∀ a ∈ s, R a b := by
    intro s _
    let r := max (s.sup Prod.fst) (s.sup (fun a => a.2.1.support.sup id)) + 1
    obtain ⟨x,hx,hbound,htail,hsep⟩ := hbad r (Nat.succ_pos _)
    refine ⟨(r,⟨x,hx⟩),⟨Nat.succ_pos _,hbound,htail,hsep⟩,?_⟩
    intro a ha
    refine ⟨(Finset.le_sup (f := Prod.fst) ha).trans_lt ((le_max_left _ _).trans_lt
      (Nat.lt_succ_self _)),?_⟩
    apply before_of_mem_afterCutoff (K := r) _ htail
    intro j hj
    exact (Finset.le_sup (f := id) hj).trans ((Finset.le_sup
      (f := fun a : ℕ × A => a.2.1.support.sup id) ha).trans
      ((le_max_right _ _).trans (Nat.le_succ _)))
  obtain ⟨w,hw,hwr⟩ := exists_seq_of_forall_finset_exists P R hs
  have hindex (i : ℕ) : i+1 ≤ (w i).1 := by
    induction i with
    | zero => exact (hw 0).1
    | succ i ih => have hh := (hwr i (i+1) (Nat.lt_succ_self i)).1; omega
  let u : BlockTestSequence D Y := {
    vector := fun i => (w i).2.1
    mem_subspace := fun i => (w i).2.2
    successive := fun i j hij => (hwr i j hij).2
    norm_bound := fun i => (intervalNorm_mono D (hindex i) _).trans (hw i).2.1
  }
  refine ⟨u,fun i => (w i).1,fun i j hij => (hwr i j hij).1,hindex,?_,
    fun i => (hw i).2.2.1,fun i => (hw i).2.2.2⟩
  intro i hi
  have hh := (hw i).2.2.2 0 (zero_mem_spreadVectorOrbit D _ _)
  have hval : (⟨denseEmbedding D (w i).2.1,(w i).2.2⟩ : Y) = 0 := by
    apply Subtype.ext
    change denseEmbedding D (u.vector i) = 0
    rw [hi, map_zero]
  rw [hval, map_zero, sub_zero, norm_zero] at hh
  exact (not_le_of_gt hε) hh

theorem eventually_spread_orbit_separated {D : ConstructionData 𝕜}
    {Y : Submodule 𝕜 (ShiftSpace D)} (u : BlockTestSequence D Y)
    (T : Y →L[𝕜] ShiftSpace D) (q : ℕ → ℕ) (hq : StrictMono q) {ε : ℝ}
    (hsep : ∀ i, ∀ z ∈ spreadVectorOrbit D (u.vector i) (q i),
      ε ≤ ‖T (u.inSubspace i)-z‖) (r : ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ z ∈ spreadVectorOrbit D (u.vector i) r,
      ε ≤ ‖T (u.inSubspace i)-z‖ := by
  filter_upwards [hq.tendsto_atTop.eventually (eventually_ge_atTop r)] with i hi
  intro z hz
  exact hsep i z (spreadVectorOrbit_mono D _ hi hz)

end ThesisCommon.GowersMaurey
