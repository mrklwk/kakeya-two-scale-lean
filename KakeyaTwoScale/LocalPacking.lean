module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Tactic

@[expose] public section

open Metric
noncomputable section
namespace KakeyaTwoScale
open Classical
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- A uniform local packing bound, constructed from one compact-ball cover.
The bound precedes all radii, centers, finite families and direction maps. -/
theorem uniform_local_packing (C : ℝ) : ∃ B : ℕ, ∀ (r : ℝ), 0 < r →
    ∀ (center : X) {J : Type*} (family : Finset J) (v : J → X),
    (∀ j ∈ family, dist (v j) center ≤ C*r) →
    (∀ j ∈ family, ∀ k ∈ family, j ≠ k → r ≤ dist (v j) (v k)) → family.card ≤ B := by
  obtain ⟨S,_,hSf,hS⟩ := (isCompact_closedBall (0:X) C).finite_cover_balls (by norm_num : (0:ℝ)<1/2)
  let centers := hSf.toFinset
  have hS' : closedBall (0:X) C ⊆ ⋃ x ∈ centers, ball x (1/2) := by simpa [centers] using hS
  refine ⟨centers.card,?_⟩
  intro r hr center J family v hbound hsep
  let z := fun j => r⁻¹ • (v j-center)
  have hz (j) (hj : j ∈ family) : z j ∈ closedBall (0:X) C := by
    rw [mem_closedBall, dist_zero_right]
    dsimp [z]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    have hb : ‖v j-center‖ ≤ C*r := by simpa [dist_eq_norm] using hbound j hj
    exact (inv_mul_le_iff₀ hr).mpr (by simpa [mul_comm] using hb)
  have hcover : ∀ j ∈ family, ∃ x ∈ centers, dist (z j) x < 1/2 := by
    intro j hj
    obtain ⟨x,hx,hzx⟩ := Set.mem_iUnion₂.mp (hS' (hz j hj))
    exact ⟨x,hx,hzx⟩
  let idx := fun j => if hj : j ∈ family then Classical.choose (hcover j hj) else (0:X)
  have hi (j) (hj : j ∈ family) : idx j ∈ centers ∧ dist (z j) (idx j) < 1/2 := by
    dsimp [idx]
    rw [dite_eq_left hj]
    exact Classical.choose_spec (hcover j hj)
  apply Finset.card_le_card_of_injOn idx (fun j hj => (hi j hj).1)
  intro j hj k hk heq
  by_contra hne
  have hlt : dist (z j) (z k) < 1 := by
    have hh := dist_triangle (z j) (idx j) (z k)
    have h₁ := (hi j hj).2
    have h₂ := (hi k hk).2
    rw [← heq, dist_comm (z k) (idx j)] at h₂
    linarith
  have he : dist (z j) (z k) = r⁻¹ * dist (v j) (v k) := by
    dsimp [z]
    rw [dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_pos hr, dist_sub_right]
  have hge : 1 ≤ dist (z j) (z k) := by
    rw [he]
    exact (le_inv_mul_iff₀ hr).mpr (by simpa using hsep j hj k hk hne)
  linarith
end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_local_packing
