import BanachIsometric.QuaternionicUnitExtension

/-! Finite-dimensional right quaternionic Hermitian norm spaces of the same
right dimension are isometric. The proof splits off actual unit lines and
extends a kernel isometry inductively, preserving the original norm/action. -/

namespace BanachIsometric.Quaternionic

noncomputable section

theorem HasHermitianSquare.onSubmodule {V : Type*} [NormedAddCommGroup V] [Module Hᵐᵒᵖ V]
    (hV : HasHermitianSquare (norm : V → ℝ)) (Y : Submodule Hᵐᵒᵖ V) :
    HasHermitianSquare (norm : Y → ℝ) := by
  obtain ⟨h, hdiag, hpos⟩ := hV
  refine ⟨h.comap Y.subtype, (fun y => hdiag y.val), ?_⟩
  intro y hy
  exact hpos y.val (fun hz => hy (Subtype.ext hz))

theorem exists_linearIsometryEquiv_of_finrank (m : ℕ)
    {V W : Type*} [NormedAddCommGroup V] [Module Hᵐᵒᵖ V] [NormSMulClass Hᵐᵒᵖ V]
    [FiniteDimensional Hᵐᵒᵖ V]
    [NormedAddCommGroup W] [Module Hᵐᵒᵖ W] [NormSMulClass Hᵐᵒᵖ W] [FiniteDimensional Hᵐᵒᵖ W]
    (hVdim : Module.finrank Hᵐᵒᵖ V = m) (hWdim : Module.finrank Hᵐᵒᵖ W = m)
    (hV : HasHermitianSquare (norm : V → ℝ)) (hW : HasHermitianSquare (norm : W → ℝ)) :
    Nonempty (V ≃ₗᵢ[Hᵐᵒᵖ] W) := by
  induction m generalizing V W with
  | zero =>
      letI : Subsingleton V := Module.finrank_zero_iff.mp hVdim
      letI : Subsingleton W := Module.finrank_zero_iff.mp hWdim
      let e := LinearEquiv.ofFinrankEq V W (hVdim.trans hWdim.symm)
      refine ⟨{ e with norm_map' := ?_ }⟩
      intro x
      rw [Subsingleton.elim x 0, e.map_zero]
      simp only [norm_zero]
  | succ m ih =>
      letI : Nontrivial V := Module.finrank_pos_iff.mp (by rw [hVdim]; exact Nat.zero_lt_succ m)
      letI : Nontrivial W := Module.finrank_pos_iff.mp (by rw [hWdim]; exact Nat.zero_lt_succ m)
      obtain ⟨D⟩ := nonempty_unitHermitianData hV
      obtain ⟨E⟩ := nonempty_unitHermitianData hW
      letI : NormSMulClass Hᵐᵒᵖ D.kernel := submoduleNormSMul D.kernel
      letI : NormSMulClass Hᵐᵒᵖ E.kernel := submoduleNormSMul E.kernel
      have hDdim : Module.finrank Hᵐᵒᵖ D.kernel = m := by
        have h := D.kernel_finrank_add_one
        rw [hVdim] at h
        omega
      have hEdim : Module.finrank Hᵐᵒᵖ E.kernel = m := by
        have h := E.kernel_finrank_add_one
        rw [hWdim] at h
        omega
      obtain ⟨g⟩ := ih hDdim hEdim D.kernel_hasHermitianSquare E.kernel_hasHermitianSquare
      exact ⟨D.extensionIsometry E g⟩

theorem exists_linearIsometryEquiv_of_finrank_eq
    {V W : Type*} [NormedAddCommGroup V] [Module Hᵐᵒᵖ V] [NormSMulClass Hᵐᵒᵖ V]
    [FiniteDimensional Hᵐᵒᵖ V]
    [NormedAddCommGroup W] [Module Hᵐᵒᵖ W] [NormSMulClass Hᵐᵒᵖ W] [FiniteDimensional Hᵐᵒᵖ W]
    (hV : HasHermitianSquare (norm : V → ℝ)) (hW : HasHermitianSquare (norm : W → ℝ))
    (hdim : Module.finrank Hᵐᵒᵖ V = Module.finrank Hᵐᵒᵖ W) :
    Nonempty (V ≃ₗᵢ[Hᵐᵒᵖ] W) :=
  exists_linearIsometryEquiv_of_finrank (Module.finrank Hᵐᵒᵖ V) rfl hdim.symm hV hW

theorem metricSubspaceHomogeneity_of_hasHermitianSquare
    {V : Type*} [NormedAddCommGroup V] [Module Hᵐᵒᵖ V] [NormSMulClass Hᵐᵒᵖ V]
    (hV : HasHermitianSquare (norm : V → ℝ)) (n : ℕ) : MetricSubspaceHomogeneity (V := V) n := by
  intro Y Z hY hZ
  letI : FiniteDimensional Hᵐᵒᵖ Y := Module.finite_of_rank_eq_nat hY
  letI : FiniteDimensional Hᵐᵒᵖ Z := Module.finite_of_rank_eq_nat hZ
  letI : NormSMulClass Hᵐᵒᵖ Y := submoduleNormSMul Y
  letI : NormSMulClass Hᵐᵒᵖ Z := submoduleNormSMul Z
  obtain ⟨e⟩ := exists_linearIsometryEquiv_of_finrank n
    (Module.finrank_eq_of_rank_eq hY) (Module.finrank_eq_of_rank_eq hZ)
    (hV.onSubmodule Y) (hV.onSubmodule Z)
  exact ⟨e.toIsometryEquiv⟩

end
end BanachIsometric.Quaternionic
