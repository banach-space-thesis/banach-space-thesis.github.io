import BanachIsometric.SphereRepetitionConeCoordinates

/-! Actual Euclidean germs of the literal strip-concatenation identities. -/

namespace BanachIsometric.SphereGenerator

open Filter
open scoped Topology unitInterval

noncomputable section

def cubeTailOfMem {n : ℕ} (z : PiolaSpace (n + 2))
    (hz : ∀ i : Fin (n + 1), z i.succ ∈ Set.Icc (0 : ℝ) 1) :
    Fin (n + 1) → unitInterval := fun i => ⟨z i.succ, hz i⟩

theorem cons_cubeTailOfMem {n : ℕ} (z : PiolaSpace (n + 2))
    (hz : ∀ i : Fin (n + 1), z i.succ ∈ Set.Icc (0 : ℝ) 1) :
    (Fin.cons (z 0) (fun i => (cubeTailOfMem z hz i : ℝ)) : PiolaSpace (n + 2)) = z := by
  ext i
  induction i using Fin.cases <;> rfl

theorem stripChart_left_cubeTailOfMem {n : ℕ} (z : PiolaSpace (n + 2))
    (hz : ∀ i : Fin (n + 1), z i.succ ∈ Set.Icc (0 : ℝ) 1)
    (hleft : z (0 : Fin (n + 1)).succ ≤ 1 / 2) :
    stripChart n 0 z = Fin.cons (z 0)
      (fun i => (leftExpandCube 0 (cubeTailOfMem z hz) i : ℝ)) := by
  ext i
  induction i using Fin.cases with
  | zero => simp
  | succ i =>
    induction i using Fin.cases with
    | zero =>
      simp only [stripChart_one, sub_zero, Fin.cons_succ, leftExpandCube, Function.update_self]
      have hm : 2 * z (0 : Fin (n + 1)).succ ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [(hz 0).1], by linarith⟩
      exact (congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hm)).symm
    | succ i => simp [leftExpandCube, cubeTailOfMem]

theorem stripChart_right_cubeTailOfMem {n : ℕ} (z : PiolaSpace (n + 2))
    (hz : ∀ i : Fin (n + 1), z i.succ ∈ Set.Icc (0 : ℝ) 1)
    (hright : 1 / 2 ≤ z (0 : Fin (n + 1)).succ) :
    stripChart n 1 z = Fin.cons (z 0)
      (fun i => (rightExpandCube 0 (cubeTailOfMem z hz) i : ℝ)) := by
  ext i
  induction i using Fin.cases with
  | zero => simp
  | succ i =>
    induction i using Fin.cases with
    | zero =>
      simp only [stripChart_one, Fin.cons_succ, rightExpandCube, Function.update_self]
      have hm : 2 * z (0 : Fin (n + 1)).succ - 1 ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith, by linarith [(hz 0).2]⟩
      exact (congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hm)).symm
    | succ i => simp [rightExpandCube, cubeTailOfMem]

theorem sphereRepetitionCone_left_of_mem (n d : ℕ) (z : PiolaSpace (n + 2))
    (hρ : 0 ≤ z 0) (hz : ∀ i : Fin (n + 1), z i.succ ∈ Set.Icc (0 : ℝ) 1)
    (hleft : z (0 : Fin (n + 1)).succ ≤ 1 / 2) :
    sphereRepetitionCone n (d + 1) (cubeSphereConeChart n z) =
      sphereRepetitionCone n d (cubeSphereConeChart n (stripChart n 0 z)) := by
  have he := sphereRepetitionCone_cubeChart_left n d hρ (cubeTailOfMem z hz) hleft
  rw [cons_cubeTailOfMem] at he
  rw [stripChart_left_cubeTailOfMem z hz hleft]
  exact he

theorem sphereRepetitionCone_right_of_mem (n d : ℕ) (z : PiolaSpace (n + 2))
    (hρ : 0 ≤ z 0) (hz : ∀ i : Fin (n + 1), z i.succ ∈ Set.Icc (0 : ℝ) 1)
    (hright : 1 / 2 < z (0 : Fin (n + 1)).succ) :
    sphereRepetitionCone n (d + 1) (cubeSphereConeChart n z) =
      cubeSphereConeChart n (stripChart n 1 z) := by
  have he := sphereRepetitionCone_cubeChart_right n d hρ (cubeTailOfMem z hz) hright
  rw [cons_cubeTailOfMem] at he
  rw [stripChart_right_cubeTailOfMem z hz hright.le]
  exact he

theorem eventually_cubeTail_mem (n : ℕ) {x : PiolaSpace (n + 2)}
    (hx : ∀ i : Fin (n + 1), x i.succ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ z in 𝓝 x, ∀ i : Fin (n + 1), z i.succ ∈ Set.Icc (0 : ℝ) 1 := by
  apply Filter.eventually_all.mpr
  intro i
  exact ((continuous_apply i.succ).continuousAt.eventually
    (isOpen_Ioo.mem_nhds (hx i))).mono (fun _ h => ⟨h.1.le, h.2.le⟩)

theorem sphereRepetitionCone_left_germ (n d : ℕ) {x : PiolaSpace (n + 2)}
    (hρ : 0 < x 0) (hx : ∀ i : Fin (n + 1), x i.succ ∈ Set.Ioo (0 : ℝ) 1)
    (hleft : x (0 : Fin (n + 1)).succ < 1 / 2) :
    ∀ᶠ z in 𝓝 x, sphereRepetitionCone n (d + 1) (cubeSphereConeChart n z) =
      sphereRepetitionCone n d (cubeSphereConeChart n (stripChart n 0 z)) := by
  have hcρ : ContinuousAt (fun z : PiolaSpace (n + 2) => z 0) x :=
    (continuous_apply (0 : Fin (n + 2))).continuousAt
  have hcl : ContinuousAt (fun z : PiolaSpace (n + 2) => z (0 : Fin (n + 1)).succ) x :=
    (continuous_apply ((0 : Fin (n + 1)).succ)).continuousAt
  have hρ' := hcρ.eventually
    (isOpen_Ioi.mem_nhds hρ)
  have hleft' := hcl.eventually
    (isOpen_Iio.mem_nhds hleft)
  filter_upwards [hρ', eventually_cubeTail_mem n hx, hleft'] with z hz htail hl
  exact sphereRepetitionCone_left_of_mem n d z hz.le htail hl.le

theorem sphereRepetitionCone_right_germ (n d : ℕ) {x : PiolaSpace (n + 2)}
    (hρ : 0 < x 0) (hx : ∀ i : Fin (n + 1), x i.succ ∈ Set.Ioo (0 : ℝ) 1)
    (hright : 1 / 2 < x (0 : Fin (n + 1)).succ) :
    ∀ᶠ z in 𝓝 x, sphereRepetitionCone n (d + 1) (cubeSphereConeChart n z) =
      cubeSphereConeChart n (stripChart n 1 z) := by
  have hcρ : ContinuousAt (fun z : PiolaSpace (n + 2) => z 0) x :=
    (continuous_apply (0 : Fin (n + 2))).continuousAt
  have hcr : ContinuousAt (fun z : PiolaSpace (n + 2) => z (0 : Fin (n + 1)).succ) x :=
    (continuous_apply ((0 : Fin (n + 1)).succ)).continuousAt
  have hρ' := hcρ.eventually
    (isOpen_Ioi.mem_nhds hρ)
  have hright' := hcr.eventually
    (isOpen_Ioi.mem_nhds hright)
  filter_upwards [hρ', eventually_cubeTail_mem n hx, hright'] with z hz htail hr
  exact sphereRepetitionCone_right_of_mem n d z hz.le htail hr

end
end BanachIsometric.SphereGenerator
