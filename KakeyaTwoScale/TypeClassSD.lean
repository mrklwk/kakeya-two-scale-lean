module
public import KakeyaTwoScale.EmpiricalEntropy

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

def coordinateProjection {I : Type*} (r : ℚ) (v : (I → ℚ) × (I → ℚ)) : I → ℚ :=
  fun i => v.1 i+r*v.2 i

theorem FiniteSDBound.coordinate_image_bound {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) {I : Type*} [Fintype I]
    (G : Finset ((I → ℚ) × (I → ℚ))) (N : ℝ) (hN : 0 ≤ N)
    (hp : ∀ r ∈ R, ((G.image (coordinateProjection r)).card:ℝ) ≤ N) :
    ((G.image (coordinateProjection (-1))).card:ℝ) ≤ C*N^β := by
  let e := Fintype.equivFin I
  let f := fun v : I → ℚ => v ∘ e.symm
  let g := fun v : (I → ℚ) × (I → ℚ) => (f v.1,f v.2)
  have hf : Function.Injective f := by
    intro v w he
    funext i
    have hh := congrFun he (e i)
    simpa [f,Function.comp_def] using hh
  have he (r : ℚ) : ((G.image g).image (vectorProjection r)).card =
      (G.image (coordinateProjection r)).card := by
    have he' : (G.image g).image (vectorProjection r) =
        (G.image (coordinateProjection r)).image f := by
      simp only [Finset.image_image,Function.comp_def]
      rfl
    rw [he',Finset.card_image_of_injective _ hf]
  have hh := hSD.vector_difference_image_bound (G.image g) N hN (by
    intro r hr
    rw [he]
    exact hp r hr)
  rwa [he] at hh

/-- Ordinary counting applied to the actual type classes and their full
projected type classes. -/
theorem FiniteSDBound.type_class_bound {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → ArithmeticPoint) (N : ℝ) (hN : 0 ≤ N)
    (hp : ∀ r ∈ R, ((wordTypeClass (arithmeticProjection r ∘ w)).card:ℝ) ≤ N) :
    ((wordTypeClass (arithmeticProjection (-1) ∘ w)).card:ℝ) ≤ C*N^β := by
  let g := fun v : I → ArithmeticPoint => (fun i => (v i).1,fun i => (v i).2)
  let G := (wordTypeClass w).image g
  have he (r : ℚ) : G.image (coordinateProjection r) = wordTypeClass (arithmeticProjection r ∘ w) := by
    rw [← wordTypeClass_image w (arithmeticProjection r)]
    simp only [G,Finset.image_image,Function.comp_def]
    rfl
  have h := hSD.coordinate_image_bound G N hN (by intro r hr; rw [he]; exact hp r hr)
  rwa [he] at h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.FiniteSDBound.coordinate_image_bound
#print axioms KakeyaTwoScale.FiniteSDBound.type_class_bound
