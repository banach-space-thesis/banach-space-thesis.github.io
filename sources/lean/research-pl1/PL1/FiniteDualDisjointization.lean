import PL1.DisjointNormingFunctionals
import BanLat.Substructures.Band.PPP

/-!
Finite dual disjointization. The projection property below is applied to the
conditionally complete strong dual, never assumed for the original lattice.
-/
noncomputable section
open scoped BigOperators
namespace PL1.FiniteDualDisjointization

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X] [HasPrincipalProjectionProperty X]

lemma exists_selecting_band (x y : X) :
    ∃ P : ProjectionBand X, P.bandProjection (x - y) = (x - y)⁺ := by
  obtain ⟨P, hP⟩ := HasPrincipalProjectionProperty.exists_projectionBand ((x - y)⁺)
  refine ⟨P, ?_⟩
  have hpos : (x-y)⁺ ∈ (P : Set X) := by
    rw [hP]
    exact Band.subset_generated _ rfl
  have hgen : (Band.generated ({(x-y)⁺} : Set X) : Set X) ⊆
      disjointComplement ({(x-y)⁻} : Set X) := by
    apply Band.generated_le (B := Band.disjointComplement ({(x-y)⁻} : Set X))
    rintro z rfl w hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    exact isVLDisjoint_posPart_negPart (x-y)
  have hneg : (x-y)⁻ ∈ disjointComplement (P : Set X) := by
    intro z hz
    have hz' : z ∈ (Band.generated ({(x-y)⁺} : Set X) : Set X) := by
      simpa [hP] using hz
    exact isVLDisjoint_comm.mp (hgen hz' _ (Set.mem_singleton _))
  calc
    P.bandProjection (x-y) = P.bandProjection ((x-y)⁺ - (x-y)⁻) := by
      rw [posPart_sub_negPart]
    _ = (x-y)⁺ := by
      rw [map_sub, P.bandProjection_eq_of_mem hpos,
        P.bandProjection_eq_zero_of_mem_dc hneg, sub_zero]

/-- Each positive finite family has a disjoint dominated refinement whose sum
majorizes every member of the original family. -/
theorem exists_disjoint_majorizing_refinement (n : ℕ) (ν : Fin n → X)
    (hν : ∀ i, 0 ≤ ν i) :
    ∃ ψ : Fin n → X, (∀ i, 0 ≤ ψ i) ∧ (∀ i, ψ i ≤ ν i) ∧
      (Pairwise fun i j => IsVLDisjoint (ψ i) (ψ j)) ∧
      (∀ i, ν i ≤ ∑ j, ψ j) := by
  classical
  induction n with
  | zero => exact ⟨ν, hν, fun i => le_rfl, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨ψ, hψ0, hψle, hψd, hψmaj⟩ := ih (fun i => ν i.succ) (fun i => hν i.succ)
    let q := ∑ i, ψ i
    obtain ⟨P, hP⟩ := exists_selecting_band (ν 0) q
    let w : Fin (n+1) → X := Fin.cons (P.bandProjection (ν 0))
      (fun i => (Pᶜ : ProjectionBand X).bandProjection (ψ i))
    have hproj0 (B : ProjectionBand X) {z : X} (hz : 0 ≤ z) : 0 ≤ B.bandProjection z :=
      Positive.zero_le_iff.mp B.bandProjection_nonneg z hz
    have hprojle (B : ProjectionBand X) {z : X} (hz : 0 ≤ z) : B.bandProjection z ≤ z :=
      Positive.le_iff.mp B.bandProjection_le_id z hz
    have hw0 (i) : 0 ≤ w i := by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hproj0 P (hν 0)
      · exact hproj0 Pᶜ (hψ0 j)
    have hwle (i) : w i ≤ ν i := by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hprojle P (hν 0)
      · exact (hprojle Pᶜ (hψ0 j)).trans (hψle j)
    have hwd : Pairwise fun i j => IsVLDisjoint (w i) (w j) := by
      intro i
      refine Fin.cases ?_ (fun a => ?_) i
      · intro j
        refine Fin.cases ?_ (fun b => ?_) j
        all_goals intro hij
        · exact False.elim (hij rfl)
        · exact isVLDisjoint_comm.mp
            ((Pᶜ : ProjectionBand X).bandProjection_mem (ψ b) _ (P.bandProjection_mem (ν 0)))
      · intro j
        refine Fin.cases ?_ (fun b => ?_) j
        all_goals intro hij
        · exact (Pᶜ : ProjectionBand X).bandProjection_mem (ψ a) _ (P.bandProjection_mem (ν 0))
        · have hab : a ≠ b := fun h => hij (congrArg Fin.succ h)
          apply IsVLDisjoint.mono_right
          · apply (hψd hab).mono_left
            rw [abs_of_nonneg (hw0 a.succ), abs_of_nonneg (hψ0 a)]
            exact hprojle Pᶜ (hψ0 a)
          · rw [abs_of_nonneg (hw0 b.succ), abs_of_nonneg (hψ0 b)]
            exact hprojle Pᶜ (hψ0 b)
    have hsum : ∑ i, w i = ν 0 ⊔ q := by
      rw [Fin.sum_univ_succ]
      change P.bandProjection (ν 0) + ∑ i, (Pᶜ : ProjectionBand X).bandProjection (ψ i) = _
      rw [← map_sum, ProjectionBand.bandProjection_compl]
      change P.bandProjection (ν 0) + (q - P.bandProjection q) = _
      have hP' : P.bandProjection (ν 0) - P.bandProjection q = (ν 0-q)⁺ := by
        rw [← map_sub, hP]
      calc
        _ = q + (ν 0-q)⁺ := by rw [← hP']; abel
        _ = ν 0 ⊔ q := (sup_eq_add_posPart_sub _ _).symm
    refine ⟨w, hw0, hwle, hwd, ?_⟩
    intro i
    rw [hsum]
    refine Fin.cases le_sup_left (fun j => ?_) i
    exact (hψmaj j).trans le_sup_right

end PL1.FiniteDualDisjointization


