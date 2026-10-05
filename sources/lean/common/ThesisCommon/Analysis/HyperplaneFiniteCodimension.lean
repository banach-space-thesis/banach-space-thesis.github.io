import ThesisCommon.Analysis.HyperplaneScalarExtension

/-! Iterating the actual hyperplane isomorphism removes any finite number
of continuous scalar equations. This supplies finite-codimension absorption
without cancelling an arbitrary Banach-space product. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem IsIsomorphicToEveryHyperplane.kernel_finite_scalar_map
    (hX : IsIsomorphicToEveryHyperplane 𝕜 X) (n : ℕ)
    (F : X →L[𝕜] (Fin n → 𝕜)) (hF : Function.Surjective F) :
    Nonempty (X ≃L[𝕜] LinearMap.ker F.toLinearMap) := by
  induction n with
  | zero =>
    let J : X →L[𝕜] LinearMap.ker F.toLinearMap :=
      (ContinuousLinearMap.id 𝕜 X).codRestrict _ (by
        intro x
        ext i
        exact Fin.elim0 i)
    exact ⟨ContinuousLinearEquiv.equivOfInverse J (LinearMap.ker F.toLinearMap).subtypeL
      (fun _ => rfl) (fun _ => Subtype.ext rfl)⟩
  | succ n ih =>
    let f : X →L[𝕜] 𝕜 := (ContinuousLinearMap.proj (0 : Fin (n+1))).comp F
    have hf : f ≠ 0 := by
      obtain ⟨x, hx⟩ := hF (Fin.cons (1 : 𝕜) (fun _ => 0))
      have he : f x = 1 := by change F x 0 = 1; rw [hx]; rfl
      intro hz
      rw [hz] at he
      simp at he
    let H := LinearMap.ker f.toLinearMap
    obtain ⟨e⟩ := hX H (scalarFunctional_closedHyperplane f hf)
    let tail : X →L[𝕜] (Fin n → 𝕜) :=
      ContinuousLinearMap.pi (fun i => (ContinuousLinearMap.proj i.succ).comp F)
    let G : X →L[𝕜] (Fin n → 𝕜) := tail.comp (H.subtypeL.comp e.toContinuousLinearMap)
    have hG : Function.Surjective G := by
      intro y
      obtain ⟨x, hx⟩ := hF (Fin.cons 0 y)
      have hxf : x ∈ H := by change F x 0 = 0; rw [hx]; rfl
      refine ⟨e.symm ⟨x, hxf⟩, ?_⟩
      ext i
      change F (e (e.symm ⟨x, hxf⟩)).val i.succ = y i
      rw [e.apply_symm_apply]
      change F x i.succ = y i
      rw [hx]
      rfl
    let V : LinearMap.ker G.toLinearMap →L[𝕜] LinearMap.ker F.toLinearMap :=
      ((H.subtypeL.comp e.toContinuousLinearMap).comp
        (LinearMap.ker G.toLinearMap).subtypeL).codRestrict _ (by
          intro y
          ext i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact (e y.val).property
          · have hy : G y.val = 0 := y.property
            exact congrFun hy j)
    let B : LinearMap.ker F.toLinearMap →L[𝕜] H :=
      (LinearMap.ker F.toLinearMap).subtypeL.codRestrict H (by
        intro y
        have hy : F y.val = 0 := y.property
        exact congrFun hy 0)
    let U : LinearMap.ker F.toLinearMap →L[𝕜] LinearMap.ker G.toLinearMap :=
      (e.symm.toContinuousLinearMap.comp B).codRestrict _ (by
        intro y
        ext i
        change F (e (e.symm (B y))).val i.succ = 0
        rw [e.apply_symm_apply]
        have hy : F y.val = 0 := y.property
        exact congrFun hy i.succ)
    have hUV (x : LinearMap.ker G.toLinearMap) : U (V x) = x := by
      apply Subtype.ext
      change e.symm (e x.val) = x.val
      exact e.symm_apply_apply x.val
    have hVU (y : LinearMap.ker F.toLinearMap) : V (U y) = y := by
      apply Subtype.ext
      change (e (e.symm (B y))).val = y.val
      rw [e.apply_symm_apply]
      rfl
    obtain ⟨a⟩ := ih G hG
    exact ⟨a.trans (ContinuousLinearEquiv.equivOfInverse V U hUV hVU)⟩

theorem IsIsomorphicToEveryHyperplane.finiteCodimension
    (hX : IsIsomorphicToEveryHyperplane 𝕜 X) (E : Submodule 𝕜 X)
    (hE : IsClosed (E : Set X)) [FiniteDimensional 𝕜 (X ⧸ E)] :
    Nonempty (X ≃L[𝕜] E) := by
  letI : IsClosed (E : Set X) := hE
  let n := Module.finrank 𝕜 (X ⧸ E)
  let e : (X ⧸ E) ≃L[𝕜] (Fin n → 𝕜) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  let q : X →L[𝕜] (X ⧸ E) := ⟨E.mkQ, continuous_quot_mk⟩
  let F : X →L[𝕜] (Fin n → 𝕜) := e.toContinuousLinearMap.comp q
  have hF : Function.Surjective F := e.surjective.comp E.mkQ_surjective
  have hk : LinearMap.ker F.toLinearMap = E := by
    ext x
    change e (E.mkQ x) = 0 ↔ x ∈ E
    rw [e.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero E
  have hh := hX.kernel_finite_scalar_map n F hF
  rwa [hk] at hh

end ThesisCommon
