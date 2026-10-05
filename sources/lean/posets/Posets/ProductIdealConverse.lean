import Posets.ProductIdealAdmissible
import Posets.ProductIdealFiniteActive
import Posets.ProductIdealCoordinate
import Posets.IdealCountTransfer

/-! The converse in Proposition 8.4, for actual closed operator ideals.
Finitely many ideals force finitely many active factors and finite incidence
posets. The remaining counts multiply to the formula in the paper. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

private def FinitePosetIdealProduct (n : ℕ) : Prop :=
  ∃ (r : ℕ) (ι : Type) (_ : Fintype ι) (P : ι → Type)
    (_ : ∀ i, Fintype (P i)) (_ : ∀ i, PartialOrder (P i))
    (_ : ∀ i, Nonempty (P i)), n = 3 ^ r * ∏ i, idealCount (P i)

private theorem finitePosetIdealProduct_one : FinitePosetIdealProduct 1 := by
  refine ⟨0, Empty, inferInstance, fun _ => PUnit, inferInstance,
    inferInstance, inferInstance, ?_⟩
  simp

private theorem finitePosetIdealProduct_three : FinitePosetIdealProduct 3 := by
  refine ⟨1, Empty, inferInstance, fun _ => PUnit, inferInstance,
    inferInstance, inferInstance, ?_⟩
  simp

private theorem finitePosetIdealProduct_poset (P : Type) [Fintype P]
    [PartialOrder P] [Nonempty P] : FinitePosetIdealProduct (idealCount P) := by
  refine ⟨0, PUnit, inferInstance, fun _ => P, inferInstance,
    inferInstance, inferInstance, ?_⟩
  simp

private theorem finitePosetIdealProduct_mul {m n : ℕ}
    (hm : FinitePosetIdealProduct m) (hn : FinitePosetIdealProduct n) :
    FinitePosetIdealProduct (m * n) := by
  obtain ⟨r, ι, hι, P, hPf, hPo, hPn, hm⟩ := hm
  obtain ⟨s, κ, hκ, Q, hQf, hQo, hQn, hn⟩ := hn
  letI := hι
  letI := hκ
  letI := hPf
  letI := hPo
  letI := hPn
  letI := hQf
  letI := hQo
  letI := hQn
  let R : ι ⊕ κ → Type := Sum.elim P Q
  letI : ∀ i, Fintype (R i) := fun i => by cases i <;> dsimp [R] <;> infer_instance
  letI : ∀ i, PartialOrder (R i) := fun i => by cases i <;> dsimp [R] <;> infer_instance
  letI : ∀ i, Nonempty (R i) := fun i => by cases i <;> dsimp [R] <;> infer_instance
  refine ⟨r + s, ι ⊕ κ, inferInstance, R, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [hm, hn, pow_add, Fintype.prod_sum_type]
  change (3 ^ r * ∏ i, idealCount (P i)) * (3 ^ s * ∏ i, idealCount (Q i)) =
    (3 ^ r * 3 ^ s) * ((∏ i, idealCount (P i)) * ∏ i, idealCount (Q i))
  ring

private theorem finitePosetIdealProduct_prod {ι : Type} [Fintype ι]
    (f : ι → ℕ) (hf : ∀ i, FinitePosetIdealProduct (f i)) :
    FinitePosetIdealProduct (∏ i, f i) := by
  have h : ∀ s : Finset ι, FinitePosetIdealProduct (∏ i ∈ s, f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using finitePosetIdealProduct_one
    | @insert a s ha ih =>
      simpa only [Finset.prod_insert ha] using finitePosetIdealProduct_mul (hf a) ih
  exact h Finset.univ

private theorem finitePosetIdealProduct_fin {n : ℕ} (h : FinitePosetIdealProduct n) :
    ∃ r k : ℕ, ∃ (P : Fin k → Type) (_ : ∀ i, Fintype (P i))
      (_ : ∀ i, PartialOrder (P i)) (_ : ∀ i, Nonempty (P i)),
      n = 3 ^ r * ∏ i, idealCount (P i) := by
  obtain ⟨r, ι, hι, P, hPf, hPo, hPn, hn⟩ := h
  letI := hι
  letI := hPf
  letI := hPo
  letI := hPn
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨r, Fintype.card ι, P ∘ e, fun i => hPf (e i),
    fun i => hPo (e i), fun i => hPn (e i), ?_⟩
  exact hn.trans (congrArg (fun t => 3 ^ r * t)
    (e.prod_comp (fun i => idealCount (P i))).symm)

/-- Necessity of the finite-poset product formula for every realization
furnished by Theorem 1.5, including the all-zero product. -/
theorem furnishedIdealCount_finite_poset_product {n : ℕ}
    (h : FurnishedIdealCount 𝕜 n) :
    ∃ r k : ℕ, ∃ (P : Fin k → Type) (_ : ∀ i, Fintype (P i))
      (_ : ∀ i, PartialOrder (P i)) (_ : ∀ i, Nonempty (P i)),
      n = 3 ^ r * ∏ i, idealCount (P i) := by
  obtain ⟨C, hCr, hCa, hCc, hCad, 𝒜, h𝒜, hreal, ⟨e⟩⟩ := h
  letI := hCr
  letI := hCa
  letI := hCc
  obtain ⟨θ, ρ, hs, _, _⟩ := hreal
  let e' := (strongSplitNontrivialIdealEquiv θ ρ hs h𝒜).trans e
  letI : Finite (ClosedIdeal 𝕜 (NormedProduct C)) := Finite.of_equiv (Fin n) e'.symm
  have hcard : Nat.card (ClosedIdeal 𝕜 (NormedProduct C)) = n := by
    simpa using Nat.card_congr e'
  obtain ⟨N, _, hN⟩ := normedProduct_finite_closedIdeal_card_reduction (𝕜 := 𝕜) C
  have hf : ∀ i : Fin N, FinitePosetIdealProduct (Nat.card (ClosedIdeal 𝕜 (C i.val))) := by
    intro i
    letI : Finite (ClosedIdeal 𝕜 (C i.val)) :=
      finite_coordinate_closedIdeals_of_finite_product (𝕜 := 𝕜) C i.val
    rcases admissible_finite_closedIdeal_count_profile (hCad i.val) with hz | hc | hp
    · letI := hz
      rw [closedIdeal_card_of_subsingleton]
      exact finitePosetIdealProduct_one
    · rw [hc.1]
      exact finitePosetIdealProduct_three
    · obtain ⟨P, hPf, hPo, hPn, hPi, _⟩ := hp
      letI := hPf
      letI := hPo
      letI := hPn
      rw [hPi]
      exact finitePosetIdealProduct_poset P
  apply finitePosetIdealProduct_fin
  rw [← hcard, hN]
  exact finitePosetIdealProduct_prod _ hf

end Posets
