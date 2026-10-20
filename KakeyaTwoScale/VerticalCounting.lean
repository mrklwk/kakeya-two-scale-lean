module
public import KakeyaTwoScale.VerticalEntropy
public import KakeyaTwoScale.DifferenceImageBound

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

theorem FiniteSDBound.vertical_image_bound {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) (hproper : ∀ s ∈ R, s ≠ -1)
    (G : Finset ArithmeticPoint) (N : ℝ) (hN : 0 ≤ N)
    (hproj : ∀ r ∈ R.image verticalSlope, ((G.image (arithmeticProjection r)).card:ℝ) ≤ N) :
    ((G.image Prod.snd).card:ℝ) ≤ C*N^β := by
  let H := G.image differenceToVertical
  have hp (s : ℚ) (hs : s ∈ R) : ((H.image (arithmeticProjection s)).card:ℝ) ≤ N := by
    have hn : 1+s ≠ 0 := by intro h; apply hproper s hs; linarith
    have he : (H.image (arithmeticProjection s)).card = (G.image (arithmeticProjection (verticalSlope s))).card := by
      rw [Finset.image_image]
      apply image_card_of_same_fibers
      intro v _ w _
      simp only [Function.comp_apply]
      rw [vertical_projection_identity s (hproper s hs) v,vertical_projection_identity s (hproper s hs) w]
      exact ⟨mul_left_cancel₀ hn,congrArg (fun z => (1+s)*z)⟩
    rw [he]
    exact hproj _ (Finset.mem_image.mpr ⟨s,hs,rfl⟩)
  have h := hSD.difference_image_bound H N hN hp
  have he : H.image (arithmeticProjection (-1)) = G.image Prod.snd := by
    simp [H,Finset.image_image,Function.comp_def,differenceToVertical,arithmeticProjection]
  rwa [he] at h

theorem finite_vertical_counting_625_373 :
    ∃ R : Finset ℚ, R.Nonempty ∧ ∀ G : Finset ArithmeticPoint, ∀ N : ℝ, 0 ≤ N →
      (∀ r ∈ R, ((G.image (arithmeticProjection r)).card:ℝ) ≤ N) →
      ((G.image Prod.snd).card:ℝ) ≤ N^(625/373:ℝ) := by
  obtain ⟨R,hproper,hSD⟩ := finiteSD_625_373_constant_one
  have hR := hSD.slopes_nonempty (by norm_num)
  refine ⟨R.image verticalSlope,hR.image _,?_⟩
  intro G N hN hproj
  simpa only [one_mul] using hSD.vertical_image_bound hproper G N hN hproj

end KakeyaTwoScale
#print axioms KakeyaTwoScale.FiniteSDBound.vertical_image_bound
#print axioms KakeyaTwoScale.finite_vertical_counting_625_373
