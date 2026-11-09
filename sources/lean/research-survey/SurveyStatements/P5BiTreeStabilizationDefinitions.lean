import SurveyStatements.P5HaarBase
import SurveyStatements.P5Support.LpHaarSequentialGeometry
import SurveyStatements.P5Support.LpHaarNormalizedTraces

/-! The coefficient conditions of LMMS Definition 3.17, with actual dyadic
indices. A signed tree consists of genuine finite dyadic blocks; its symbol
is the exact normalized double block average, not a prescribed array. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory
open scoped ENNReal BigOperators

namespace SurveyStatements.P5.BiTree

open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

def child (I : DyadicIndex) (b : Bool) : DyadicIndex :=
  ⟨I.1 + 1, if b then lpHaarLeftIndex I.1 I.2 else lpHaarRightIndex I.1 I.2⟩

def root : DyadicIndex := ⟨0, ⟨0, by decide⟩⟩

@[simp] theorem child_level (I : DyadicIndex) (b : Bool) : (child I b).1 = I.1 + 1 := rfl

/-- Exactly the five coefficient conditions in LMMS Definition 3.17.
Lower and upper conditions are strict, as in the source; the diagonal and
superdiagonal conditions are non-strict. -/
structure SemiStable (d : DyadicIndex → DyadicIndex → 𝕜)
    (η : ℕ → ℕ → ℝ) (δ : ℝ) : Prop where
  lower : ∀ I J b, J.1 ≤ I.1 → ‖d (child I b) J - d I J‖ < η I.1 J.1
  upper : ∀ I J b, I.1 < J.1 → ‖d I (child J b) - d I J‖ < η I.1 J.1
  diagonal : ∀ I J b c, I.1 = J.1 →
    ‖d (child I b) (child J c) - d I J‖ ≤ η I.1 I.1
  superdiagonal : ∀ I J b c, J.1 = I.1 + 1 →
    ‖d (child I b) (child J c) - d I J‖ ≤ η I.1 (I.1 + 1)
  balance : ‖d root (child root true) - d root (child root false)‖ < δ

abbrev SignedTree := LpHaarSequentialSplits

def SignedTree.block (F : SignedTree) (I : DyadicIndex) : LpHaarFiniteSplit :=
  F.node (lpHaarHeapIndex I.1 I.2)

def blockAverage (d : DyadicIndex → DyadicIndex → 𝕜)
    (S T : LpHaarFiniteSplit) : 𝕜 :=
  (S.atoms.card : 𝕜)⁻¹ * (T.atoms.card : 𝕜)⁻¹ *
    ∑ k ∈ S.atoms, ∑ l ∈ T.atoms, d ⟨S.level, k⟩ ⟨T.level, l⟩

def compressedSymbol (d : DyadicIndex → DyadicIndex → 𝕜)
    (Fo Fi : SignedTree) (I J : DyadicIndex) : 𝕜 :=
  blockAverage d (Fo.block I) (Fi.block J)

theorem SignedTree.block_child_parent (F : SignedTree) (I : DyadicIndex) (b : Bool) :
    (F.block (child I b)).parent.set = ((F.block I).child b).set := by
  cases b
  · exact F.cell_right I.1 I.2
  · exact F.cell_left I.1 I.2

end SurveyStatements.P5.BiTree
