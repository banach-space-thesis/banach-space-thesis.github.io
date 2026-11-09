import ThesisCommon.Analysis.LpHaarFiniteSplits
import ThesisCommon.Analysis.OrderedFiniteHistory

/-! An infinite binary system of genuine signed dyadic blocks selected
from ordered finite histories. The parent of each node is a child of an
earlier node. Two-sided interference selection is performed on actual
bounded functionals and Lp vectors at every step. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical
namespace ThesisCommon

def lpHaarHistoryParent (n : ℕ) (h : Fin n → LpHaarFiniteSplit) : LpHaarFiniteParent :=
  if hn : n = 0 then LpHaarFiniteParent.root else
    (h ⟨(n - 1) / 2, by omega⟩).child (decide (n % 2 = 1))

structure LpHaarSequentialSplits where
  node : ℕ → LpHaarFiniteSplit
  level : ∀ j, j ≤ (node j).level
  parent : ∀ j, (node j).parent.set =
    (lpHaarHistoryParent j (fun i : Fin j => node i.val)).set

namespace LpHaarSequentialSplits

theorem root_set (F : LpHaarSequentialSplits) :
    (F.node 0).parent.set = LpHaarFiniteParent.root.set := by
  simpa only [lpHaarHistoryParent, dif_pos rfl] using F.parent 0

theorem left_parent (F : LpHaarSequentialSplits) (j : ℕ) :
    (F.node (2 * j + 1)).parent.set = ((F.node j).child true).set := by
  have h := F.parent (2 * j + 1)
  have hn : 2 * j + 1 ≠ 0 := by omega
  have hparent : (2 * j + 1 - 1) / 2 = j := by omega
  have hparity : (2 * j + 1) % 2 = 1 := by omega
  simpa only [lpHaarHistoryParent, dif_neg hn, hparent, hparity, decide_true] using h

theorem right_parent (F : LpHaarSequentialSplits) (j : ℕ) :
    (F.node (2 * j + 2)).parent.set = ((F.node j).child false).set := by
  have h := F.parent (2 * j + 2)
  have hn : 2 * j + 2 ≠ 0 := by omega
  have hparent : (2 * j + 2 - 1) / 2 = j := by omega
  have hparity : (2 * j + 2) % 2 ≠ 1 := by omega
  simpa only [lpHaarHistoryParent, dif_neg hn, hparent, hparity, decide_false] using h

end LpHaarSequentialSplits

theorem exists_haar_split_history
    (R : (j : ℕ) → LpHaarFiniteParent → (Fin j → LpHaarFiniteSplit) → LpHaarFiniteSplit → Prop)
    (hnext : ∀ j P h, ∃ S : LpHaarFiniteSplit,
      j ≤ S.level ∧ S.parent.set = P.set ∧ R j P h S) :
    ∃ F : LpHaarSequentialSplits, ∀ j,
      R j (lpHaarHistoryParent j (fun i : Fin j => F.node i.val))
        (fun i : Fin j => F.node i.val) (F.node j) := by
  obtain ⟨r, hr⟩ := exists_sequence_with_history
    (fun j h S => j ≤ S.level ∧ S.parent.set = (lpHaarHistoryParent j h).set ∧
      R j (lpHaarHistoryParent j h) h S)
    (fun j h => hnext j (lpHaarHistoryParent j h) h)
  exact ⟨⟨r, fun j => (hr j).1, fun j => (hr j).2.1⟩, fun j => (hr j).2.2⟩

theorem lpHaar_infinite_two_sided_selection (𝕜 : Type*) [RCLike 𝕜]
    (p : BanachExponent) (hp : p.val ≠ ∞) (T : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (ε : (j : ℕ) → LpHaarFiniteParent → (Fin j → LpHaarFiniteSplit) → ℝ)
    (hε : ∀ j P h, 0 < ε j P h) :
    ∃ F : LpHaarSequentialSplits, ∀ j (i : Fin j),
      ‖(F.node i.val).reader 𝕜 p (T ((F.node j).vector 𝕜 p))‖ <
          ε j (lpHaarHistoryParent j (fun k : Fin j => F.node k.val))
            (fun k : Fin j => F.node k.val) ∧
      ‖(F.node j).reader 𝕜 p (T ((F.node i.val).vector 𝕜 p))‖ <
          ε j (lpHaarHistoryParent j (fun k : Fin j => F.node k.val))
            (fun k : Fin j => F.node k.val) := by
  apply exists_haar_split_history
    (fun j P h S => ∀ i : Fin j,
      ‖(h i).reader 𝕜 p (T (S.vector 𝕜 p))‖ < ε j P h ∧
        ‖S.reader 𝕜 p (T ((h i).vector 𝕜 p))‖ < ε j P h)
  intro j P h
  obtain ⟨S, hlevel, hparent, hf, hb⟩ := lpHaarFiniteParent_select 𝕜 p hp
    (fun i : Fin j => ((h i).reader 𝕜 p).comp T)
    (fun i : Fin j => T ((h i).vector 𝕜 p)) P j (hε j P h)
  exact ⟨S, hlevel, hparent, fun i => ⟨hf i, hb i⟩⟩

end ThesisCommon
