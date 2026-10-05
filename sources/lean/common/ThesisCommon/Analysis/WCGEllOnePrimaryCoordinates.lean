import ThesisCommon.Analysis.WCGEllOneIteratedSelection
import ThesisCommon.Analysis.CountableLpBlocks
import ThesisCommon.Analysis.FullCountablePartition
import ThesisCommon.Analysis.LpPartitionCoordinates

/-! Every projection on the iterated WCG ℓ1 sum admits actual isometric
coordinates whose diagonal entries are projections on the countable model.
Hajnal selection then removes the off-diagonal interactions on a full set. -/
noncomputable section
open scoped Cardinal ENNReal
namespace ThesisCommon
universe u
variable {𝕜 X : Type*} {Γ : Type u} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem IsWeaklyCompactlyGenerated.iterated_ellOne_primary_coordinates
    (hX : IsWeaklyCompactlyGenerated 𝕜 X)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (P : lp (fun _ : Γ => lp (fun _ : ℕ => X) 1) 1 →L[𝕜]
      lp (fun _ : Γ => lp (fun _ : ℕ => X) 1) 1) (hP : P.comp P = P) :
    ∃ E : lp (fun _ : Γ => lp (fun _ : ℕ => X) 1) 1 ≃ₗᵢ[𝕜]
        lp (fun _ : Γ => lp (fun _ : ℕ => X) 1) 1,
      (∀ γ, (lpCoordinateEntry 1 (operatorTransport E E P) γ γ).comp
        (lpCoordinateEntry 1 (operatorTransport E E P) γ γ) =
          lpCoordinateEntry 1 (operatorTransport E E P) γ γ) ∧
      ∃ H : Set Γ, Cardinal.mk H = Cardinal.mk Γ ∧
        ∀ α ∈ H, ∀ β ∈ H, α ≠ β →
          ((lpCoordinateProjection (𝕜 := 𝕜) 1 {β}).comp (operatorTransport E E P)).comp
            (lpCoordinateProjection (𝕜 := 𝕜) 1 {α}) = 0 := by
  classical
  have hs (α : Γ) := hX.iterated_ellOne_operator_countable_support
    (P.comp (lp.singleContinuousLinearMap (𝕜 := 𝕜) (p := 1)
      (E := fun _ : Γ => lp (fun _ : ℕ => X) 1) α))
  choose F hF hPF using hs
  obtain ⟨B, ⟨hB, hBcount, hcover⟩, _htri, hproj, _hcount⟩ :=
    exists_lp_triangular_countable_blocks 1 (by norm_num) P hP F hF hPF
  obtain ⟨D, hD, hDcount, hDne, hDcover, hDproj⟩ := countable_partition_nonempty_reindex
    B (Cardinal.aleph0_lt_aleph_one.trans hΓ) (Cardinal.mk_ord_toType _)
    hB hBcount hcover (fun A => (lpBlockCompression 1 P A).comp
      (lpBlockCompression 1 P A) = lpBlockCompression 1 P A) hproj
  have hφ (γ : Γ) : Nonempty (D γ × ℕ ≃ ℕ) := by
    letI : Countable (D γ) := (hDcount γ).to_subtype
    letI : Nonempty (D γ) := (hDne γ).to_subtype
    exact ⟨countableBlockIndexEquiv (D γ)⟩
  let φ (γ : Γ) : D γ × ℕ ≃ ℕ := Classical.choice (hφ γ)
  let E := lpPartitionReadIsometry (𝕜 := 𝕜) (X := X) 1 (by norm_num) D hD hDcover φ
  exact ⟨E, fun γ => lpPartitionReadIsometry_entry_idempotent 1 (by norm_num)
    D hD hDcover φ P γ (hDproj γ),
    hX.iterated_ellOne_diagonal_coordinates hΓ (operatorTransport E E P)⟩

end ThesisCommon
