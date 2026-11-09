import CKEUPFP.CantorAtoms
import CKEUPFP.CantorSelectedFactors
import CKEUPFP.CantorCompression
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The quantitative Cantor transfer theorem

The diagonal field is constructed from the given operator using the no-c₀
hypothesis. Its proved Borelness and shrinking local defects feed localization
and selection. Thus this theorem has exactly the paper's assumptions, without
an atom-field, extension, or selection hypothesis supplied by the caller.
-/

noncomputable section

open TopologicalSpace
open scoped Topology

namespace CKEUPFP

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [SeparableSpace E]

/-- Section 4: CPFP transfers from E to C(Cantor,E), with constant 4C/3. -/
theorem cantorQuantitativeTransfer : CantorQuantitativeTransfer 𝕜 E := by
  intro hno C hC
  have hCpos : 0 < C := zero_lt_one.trans_le hC.1
  let η : ℝ := 1 / (4 * C)
  have hηpos : 0 < η := one_div_pos.mpr (mul_pos (by norm_num) hCpos)
  have hquarter : C * η ≤ (1 / 4 : ℝ) := by
    dsimp [η]
    field_simp
    norm_num
  letI : MetricSpace CantorSpace := PiNat.metricSpace
  letI : Uncountable CantorSpace := by
    apply uncountable_iff_forall_not_surjective.mpr
    intro f hf
    let d : CantorSpace := fun n => if f n n = 0 then 1 else 0
    obtain ⟨n, hn⟩ := hf d
    have hdiag : f n n ≠ d n := by
      by_cases hz : f n n = 0 <;> simp [d, hz]
    exact hdiag (congrFun hn n)
  letI : MeasurableSpace CantorSpace := borel CantorSpace
  letI : BorelSpace CantorSpace := ⟨rfl⟩
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  refine ⟨by linarith [hC.1], fun T => ?_⟩
  let A := cantorAtomField T
  have hsmall : ∀ t : CantorSpace, ∃ U : Set CantorSpace,
      IsOpen U ∧ t ∈ U ∧ localDefect T A U t < η := by
    intro t
    obtain ⟨n, hn⟩ := exists_cantorCylinder_localDefect_lt hno T t hηpos
    exact ⟨PiNat.cylinder t n, (isClopen_cantorCylinder t n).isOpen,
      PiNat.self_mem_cylinder t n, hn⟩
  obtain ⟨O, σ, e, L, R, hO, he, hinj, hA, hL, hR, hbounds, hloc, hfactor⟩ :=
    selected_local_factors_on_cantor T A
      (M := ‖T‖₊) (norm_cantorAtomField_le hno T)
      (measurable_cantorAtomField_apply hno T) η hsmall hC
  let D : Set CantorSpace := Set.range e
  have hDcompact : IsCompact D := isCompact_range he
  have hDclosed : IsClosed D := hDcompact.isClosed
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hDcompact
  have hDnonempty : D.Nonempty := ⟨e (fun _ => 0), ⟨fun _ => 0, rfl⟩⟩
  have hDO : D ⊆ O := by
    rintro d ⟨t, rfl⟩
    exact (hloc t).1
  let hmodel : CantorSpace ≃ₜ D := (he.isClosedEmbedding hinj).isEmbedding.toHomeomorph
  have heval (d : D) : e (hmodel.symm d) = d.val := by
    exact congrArg Subtype.val (hmodel.apply_symm_apply d)
  let LD : D → E →L[𝕜] E := fun d => L (hmodel.symm d)
  let RD : D → E →L[𝕜] E := fun d => R (hmodel.symm d)
  have hAD : IsStronglyContinuous (fun d : D => A d) := by
    intro x
    have hc := (hA x).comp hmodel.symm.continuous
    simpa only [Function.comp_def, heval] using hc
  have hLD : IsStronglyContinuous LD := fun x => (hL x).comp hmodel.symm.continuous
  have hRD : IsStronglyContinuous RD := fun x => (hR x).comp hmodel.symm.continuous
  have hfacD : ∀ d : D,
      ((LD d).comp (factorSelectionSide σ (A d))).comp (RD d) =
        ContinuousLinearMap.id 𝕜 E := by
    intro d
    simpa only [LD, RD, heval] using hfactor (hmodel.symm d)
  have hlocD : ∀ d : D, localDefect T A O d ≤ η := by
    intro d
    simpa only [heval] using (hloc (hmodel.symm d)).2
  have hfact := cantor_factorisation_of_selected_fields T A hDclosed hDnonempty hO hDO
    hmodel σ LD RD hC.1 hηpos.le hquarter hAD
    (fun d => norm_cantorAtomField_le hno T d) hLD hRD
    (fun d => (hbounds (hmodel.symm d)).1) (fun d => (hbounds (hmodel.symm d)).2)
    hfacD hlocD
  have hcost : (4 / 3 : ℝ) * C = 4 * C / 3 := by ring
  rw [hcost] at hfact
  cases σ
  · exact Or.inl hfact
  · exact Or.inr hfact

end CKEUPFP
