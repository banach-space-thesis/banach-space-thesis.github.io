import ThesisCommon.Analysis.LpHaarParentSelection
import ThesisCommon.Analysis.LpHaarSignedChildIndices

/-! Concrete nonempty dyadic parents and their signed binary splits.
These data carry finite sets, actual Lp vectors and actual bounded readers. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace ThesisCommon

structure LpHaarFiniteParent where
  level : ℕ
  atoms : Finset (Fin (2 ^ level))
  nonempty : atoms.Nonempty

namespace LpHaarFiniteParent

def root : LpHaarFiniteParent := ⟨0, {⟨0, by decide⟩}, Finset.singleton_nonempty _⟩

def set (P : LpHaarFiniteParent) : Set ℝ := lpHaarBlockParent P.level P.atoms

theorem measurable (P : LpHaarFiniteParent) : MeasurableSet P.set :=
  P.atoms.measurableSet_biUnion (fun _ _ => measurableSet_Ioc)

theorem root_set : root.set = lpHaarCell 0 0 := by
  simp [set, root, lpHaarBlockParent]

theorem mass_pos (P : LpHaarFiniteParent) :
    0 < (volume.restrict (Icc (0 : ℝ) 1)).real P.set := by
  rw [set, lpHaarBlockParent_real_measure]
  exact mul_pos (by exact_mod_cast Finset.card_pos.mpr P.nonempty)
    (intervalLpDyadicRadius_pos P.level)

end LpHaarFiniteParent

structure LpHaarFiniteSplit where
  level : ℕ
  atoms : Finset (Fin (2 ^ level))
  signs : Fin (2 ^ level) → Bool
  nonempty : atoms.Nonempty

namespace LpHaarFiniteSplit

def parent (S : LpHaarFiniteSplit) : LpHaarFiniteParent := ⟨S.level, S.atoms, S.nonempty⟩

def child (S : LpHaarFiniteSplit) (b : Bool) : LpHaarFiniteParent :=
  ⟨S.level + 1, lpHaarSignedChildAtoms S.level S.atoms
      (if b then S.signs else fun k => !(S.signs k)),
    lpHaarSignedChildAtoms_nonempty S.level S.atoms S.nonempty _⟩

theorem child_set (S : LpHaarFiniteSplit) (b : Bool) :
    (S.child b).set = lpHaarSignedPart S.level S.atoms
      (if b then S.signs else fun k => !(S.signs k)) :=
  lpHaarSignedChildAtoms_parent _ _ _

theorem children_union (S : LpHaarFiniteSplit) :
    (S.child true).set ∪ (S.child false).set = S.parent.set := by
  simpa only [child_set, if_true, Bool.false_eq_true, if_false] using
    lpHaarSignedPart_union S.level S.atoms S.signs

theorem children_disjoint (S : LpHaarFiniteSplit) :
    Disjoint (S.child true).set (S.child false).set := by
  simpa only [child_set, if_true, Bool.false_eq_true, if_false] using
    lpHaarSignedPart_disjoint S.level S.atoms S.signs

theorem child_mass (S : LpHaarFiniteSplit) (b : Bool) :
    (volume.restrict (Icc (0 : ℝ) 1)).real (S.child b).set =
      (volume.restrict (Icc (0 : ℝ) 1)).real S.parent.set / 2 := by
  rw [LpHaarFiniteParent.set, lpHaarBlockParent_real_measure]
  change ((lpHaarSignedChildAtoms S.level S.atoms
    (if b then S.signs else fun k => !(S.signs k))).card : ℝ) *
      intervalLpDyadicRadius (S.level + 1) = _
  rw [lpHaarSignedChildAtoms_mass, LpHaarFiniteParent.set, lpHaarBlockParent_real_measure]
  rfl

def vector (S : LpHaarFiniteSplit) (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) : IntervalLp 𝕜 p :=
  lpHaarSignedBlock 𝕜 p S.level S.atoms S.signs

def reader (S : LpHaarFiniteSplit) (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) :
    IntervalLp 𝕜 p →L[𝕜] 𝕜 := lpHaarSignedBlockReader 𝕜 p S.level S.atoms S.signs

end LpHaarFiniteSplit

theorem lpHaarFiniteParent_select (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
    {a b : ℕ} (φ : Fin a → IntervalLp 𝕜 p →L[𝕜] 𝕜) (f : Fin b → IntervalLp 𝕜 p)
    (P : LpHaarFiniteParent) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : LpHaarFiniteSplit, N ≤ S.level ∧ S.parent.set = P.set ∧
      (∀ i, ‖φ i (S.vector 𝕜 p)‖ < ε) ∧ ∀ i, ‖S.reader 𝕜 p (f i)‖ < ε := by
  obtain ⟨n, hn, A, θ, hA, heq, hf, hb⟩ := lpHaarParent_select_small 𝕜 p hp φ f
    P.level P.atoms P.nonempty N hε
  exact ⟨⟨n, A, θ, hA⟩, hn, heq, hf, hb⟩

end ThesisCommon
