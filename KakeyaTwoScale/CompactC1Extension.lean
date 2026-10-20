module
public import KakeyaTwoScale.OpenSignGraphFibers
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

open Set Filter Function
open scoped Topology
noncomputable section
namespace KakeyaTwoScale

/-- A compact subset of an open C1 domain admits a global C1 extension agreeing
on a neighborhood of every source point. No quantitative cutoff bound is used. -/
theorem compact_contDiff_extension {n k : ℕ}
    (F : (Fin n → ℝ) → (Fin k → ℝ)) (U S : Set (Fin n → ℝ))
    (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ G : (Fin n → ℝ) → (Fin k → ℝ), ContDiff ℝ 1 G ∧
      ∀ x ∈ S, G =ᶠ[𝓝 x] F := by
  obtain ⟨V,hV,hSV,hVU,_⟩ := exists_open_between_and_isCompact_closure hS hU hSU
  obtain ⟨W,hW,hSW,hWV,_⟩ := exists_open_between_and_isCompact_closure hS hV hSV
  obtain ⟨c,hc,_,hcs,hcone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (1 : ℕ∞)) hV isClosed_closure hWV
  let G : (Fin n → ℝ) → (Fin k → ℝ) := fun x => c x • F x
  have heq (x : Fin n → ℝ) (hx : x ∈ S) : G =ᶠ[𝓝 x] F := by
    filter_upwards [hW.mem_nhds (hSW hx)] with y hy
    simp only [G,(hcone y).mp (subset_closure hy),one_smul]
  refine ⟨G,contDiff_iff_contDiffAt.mpr (fun x => ?_),heq⟩
  by_cases hx : x ∈ U
  · exact hc.contDiffAt.smul ((hF x hx).contDiffAt (hU.mem_nhds hx))
  · have hxV : x ∉ closure V := fun h => hx (hVU h)
    have he : G =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxV] with y hy
      have hyV : y ∉ V := fun h => hy (subset_closure h)
      have hcy : c y = 0 := notMem_support.mp (hcs ▸ hyV)
      simp only [G,hcy,zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq he

end KakeyaTwoScale
#print axioms KakeyaTwoScale.compact_contDiff_extension
