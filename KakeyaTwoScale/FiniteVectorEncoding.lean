module
public import KakeyaTwoScale.FiveStepBound
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- A single rational linear functional is injective on any specified
finite collection of vectors. This is finite-set encoding, not a linear
embedding of the whole vector space. -/
theorem exists_finite_vector_encoder (n : ℕ) (S : Finset (Fin n → ℚ)) :
    ∃ f : (Fin n → ℚ) →ₗ[ℚ] ℚ, Set.InjOn f (↑S : Set (Fin n → ℚ)) := by
  induction n with
  | zero =>
    refine ⟨0,?_⟩
    intro x _ y _ _
    exact Subsingleton.elim _ _
  | succ n ih =>
    let tail := fun x : Fin (n+1) → ℚ => fun i : Fin n => x i.succ
    obtain ⟨f,hf⟩ := ih (S.image tail)
    let bad := ((S.product S).filter (fun v => f (tail v.1) ≠ f (tail v.2))).image
      (fun v => (v.2 0-v.1 0)/(f (tail v.1)-f (tail v.2)))
    obtain ⟨b,hb⟩ := Infinite.exists_notMem_finset bad
    let g : (Fin (n+1) → ℚ) →ₗ[ℚ] ℚ :=
      { toFun := fun x => x 0+b*f (tail x)
        map_add' := by
          intro x y
          have he : tail (x+y) = tail x+tail y := rfl
          simp only [he,map_add,Pi.add_apply]
          ring
        map_smul' := by
          intro c x
          have he : tail (c • x) = c • tail x := rfl
          simp only [he,map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
          ring }
    refine ⟨g,?_⟩
    intro x hx y hy he
    have he' : x 0+b*f (tail x) = y 0+b*f (tail y) := he
    have ht : f (tail x) = f (tail y) := by
      by_contra hn
      apply hb
      apply Finset.mem_image.mpr
      refine ⟨(x,y),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,hn⟩,?_⟩
      apply (div_eq_iff (sub_ne_zero.mpr hn)).mpr
      linear_combination -he'
    have htail : tail x = tail y := hf
      (Finset.mem_image.mpr ⟨x,hx,rfl⟩) (Finset.mem_image.mpr ⟨y,hy,rfl⟩) ht
    have hzero : x 0 = y 0 := by rw [ht] at he'; linarith
    funext i
    refine Fin.cases hzero (fun j => ?_) i
    exact congrFun htail j

def vectorProjection {n : ℕ} (r : ℚ) (v : (Fin n → ℚ) × (Fin n → ℚ)) : Fin n → ℚ :=
  v.1+r • v.2

def encodeVectorPair {n : ℕ} (f : (Fin n → ℚ) →ₗ[ℚ] ℚ)
    (v : (Fin n → ℚ) × (Fin n → ℚ)) : ArithmeticPoint := (f v.1,f v.2)

theorem encoder_projection {n : ℕ} (f : (Fin n → ℚ) →ₗ[ℚ] ℚ)
    (r : ℚ) (v : (Fin n → ℚ) × (Fin n → ℚ)) :
    arithmeticProjection r (encodeVectorPair f v) = f (vectorProjection r v) := by
  simp [arithmeticProjection,encodeVectorPair,vectorProjection]

/-- One encoder simultaneously preserves cardinalities of all selected
projection images, including the distinguished difference coordinate. -/
theorem exists_projection_encoder {n : ℕ}
    (G : Finset ((Fin n → ℚ) × (Fin n → ℚ))) (R : Finset ℚ) :
    ∃ f : (Fin n → ℚ) →ₗ[ℚ] ℚ,
      ∀ r ∈ R, Set.InjOn f (↑(G.image (vectorProjection r)) : Set (Fin n → ℚ)) ∧
        ((G.image (encodeVectorPair f)).image (arithmeticProjection r)).card =
          (G.image (vectorProjection r)).card := by
  obtain ⟨f,hf⟩ := exists_finite_vector_encoder n (R.biUnion (fun r => G.image (vectorProjection r)))
  refine ⟨f,?_⟩
  intro r hr
  have hi : Set.InjOn f (↑(G.image (vectorProjection r)) : Set (Fin n → ℚ)) := by
    intro x hx y hy he
    exact hf (Finset.mem_biUnion.mpr ⟨r,hr,hx⟩) (Finset.mem_biUnion.mpr ⟨r,hr,hy⟩) he
  refine ⟨hi,?_⟩
  have he : (G.image (encodeVectorPair f)).image (arithmeticProjection r) =
      (G.image (vectorProjection r)).image f := by
    simp only [Finset.image_image,Function.comp_def,encoder_projection]
  rw [he]
  exact Finset.card_image_iff.mpr hi

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_finite_vector_encoder
#print axioms KakeyaTwoScale.encoder_projection
#print axioms KakeyaTwoScale.exists_projection_encoder
