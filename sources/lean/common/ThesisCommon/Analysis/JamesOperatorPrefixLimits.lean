import ThesisCommon.Analysis.JamesAndrewArraySelection

/-! The two concrete coordinate limits needed for Andrew selection of
images of constant prefixes. They follow from the constructed bidual. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ⊤)
  (hpl : 1 < p.val.toReal)

def jamesOperatorPrefixLimit (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) : ℕ → 𝕜 :=
  jamesBidualCoordinate p (bidualMap T (jamesBidualConstant (𝕜 := 𝕜) p hp hpl))

theorem jamesOperatorPrefixLimit_coordinate_tendsto
    (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) (k : ℕ) :
    Tendsto (fun n => T (jamesConstantPrefix p hp n) k) atTop
      (𝓝 (jamesOperatorPrefixLimit p hp hpl T k)) := by
  exact boundedWeakCauchyBidual_tendsto (jamesConstantPrefix (𝕜 := 𝕜) p hp)
    (fun φ => cauchySeq_tendsto_of_complete (jamesConstantPrefix_weakCauchy p hp hpl φ))
    (jamesConstantPrefix_norm_le p hp)
    ((JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) k).comp T)

theorem jamesOperatorPrefixLimit_tendsto
    (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) :
    Tendsto (jamesOperatorPrefixLimit p hp hpl T) atTop
      (𝓝 (jamesOperatorScalar p hp hpl T)) :=
  jamesBidualCoordinate_tendsto p hp _

theorem jamesOperatorPrefix_selected_matrix
    (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p)
    (w : ℕ → ℝ) (hw : ∀ n, 0 < w n) :
    ∃ α β : ℕ → ℕ, StrictMono α ∧ StrictMono β ∧
      (∀ i, ‖jamesOperatorPrefixLimit p hp hpl T (α i) - jamesOperatorScalar p hp hpl T‖ < w i) ∧
      (∀ i j, ‖T (jamesConstantPrefix p hp (β j)) (α i) -
        (if i ≤ j then jamesOperatorPrefixLimit p hp hpl T (α i) else 0)‖ < w i * w j) :=
  exists_andrew_array_subsequences (fun n k => T (jamesConstantPrefix p hp n) k)
    (jamesOperatorPrefixLimit p hp hpl T) (jamesOperatorScalar p hp hpl T) w
    (fun n => (T (jamesConstantPrefix p hp n)).tendsto_zero)
    (jamesOperatorPrefixLimit_coordinate_tendsto p hp hpl T)
    (jamesOperatorPrefixLimit_tendsto p hp hpl T) hw

end ThesisCommon
