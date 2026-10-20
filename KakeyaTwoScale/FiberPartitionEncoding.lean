module
public import KakeyaTwoScale.HomogeneousPartition

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

def fiberCardPartition {A B : Type*} [DecidableEq B] (S : Finset A) (f : A → B) (p : ℝ) : ℝ :=
  ∑ y ∈ S.image f, ((S.filter (fun x => f x=y)).card:ℝ)^p

/-- Exact transport of the occupied-fiber power sum through an actual
injective encoding preserving the height equivalence relation. -/
theorem fiberCardPartition_encoding {A B C D : Type*} [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (S : Finset A) (e : A → B) (f : A → C) (g : B → D)
    (he : Set.InjOn e (↑S : Set A))
    (h : ∀ x ∈ S, ∀ y ∈ S, g (e x)=g (e y) ↔ f x=f y) (p : ℝ) :
    fiberCardPartition (S.image e) g p = fiberCardPartition S f p := by
  have hr : ∀ b : {b // b ∈ S.image f}, ∃ x, x ∈ S ∧ f x=b.val := by
    intro b
    exact Finset.mem_image.mp b.property
  choose rep hrep using hr
  unfold fiberCardPartition
  symm
  apply Finset.sum_bij (fun b hb => g (e (rep ⟨b,hb⟩)))
  · intro b hb
    exact Finset.mem_image.mpr ⟨_,Finset.mem_image.mpr ⟨_,(hrep ⟨b,hb⟩).1,rfl⟩,rfl⟩
  · intro b hb c hc heq
    have hh := (h _ (hrep ⟨b,hb⟩).1 _ (hrep ⟨c,hc⟩).1).mp heq
    simpa only [(hrep ⟨b,hb⟩).2,(hrep ⟨c,hc⟩).2] using hh
  · intro c hc
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    have hb : f v ∈ S.image f := Finset.mem_image.mpr ⟨v,hv,rfl⟩
    refine ⟨f v,hb,?_⟩
    exact (h _ (hrep ⟨f v,hb⟩).1 v hv).mpr (hrep ⟨f v,hb⟩).2
  · intro b hb
    have hh := encoded_fiber_card S e f g he h (rep ⟨b,hb⟩) (hrep ⟨b,hb⟩).1
    rw [(hrep ⟨b,hb⟩).2] at hh
    convert congrArg (fun k : ℕ => (k:ℝ)^p) hh.symm using 1 <;> congr 1 <;> congr 1 <;> congr 1 <;> ext x <;> simp

/-- The scalar theorem extends to every finite rational vector dimension
with the same slope family, using the existing finite integer encoder. -/
theorem finite_homogeneous_vector_partition_625_373 :
    ∃ R : Finset ℚ, R.Nonempty ∧ ∀ n : ℕ,
      ∀ G : Finset ((Fin n → ℚ) × (Fin n → ℚ)), G.Nonempty →
      ∃ r ∈ R, fiberCardPartition G Prod.snd (252/373) ≤
        ((G.image (vectorProjection r)).card:ℝ)^(625/373:ℝ) := by
  obtain ⟨R,hR,hscalar⟩ := finite_homogeneous_partition_625_373
  refine ⟨R,hR,?_⟩
  intro n G hG
  obtain ⟨e,he,hv,hp⟩ := exists_integer_vector_encoder G R
  obtain ⟨r,hr,hh⟩ := hscalar (G.image e) (hG.image e)
  have hpart := fiberCardPartition_encoding G e Prod.snd Prod.snd he hv (252/373)
  have hcard : ((G.image e).image (integerProjection r)).card = (G.image (vectorProjection r)).card := by
    rw [Finset.image_image]
    exact image_card_of_same_fibers G (integerProjection r ∘ e) (vectorProjection r) (hp r hr)
  change fiberCardPartition (G.image e) Prod.snd (252/373) ≤ _ at hh
  rw [hpart,hcard] at hh
  exact ⟨r,hr,hh⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.fiberCardPartition_encoding
#print axioms KakeyaTwoScale.finite_homogeneous_vector_partition_625_373
