module
public import KakeyaTwoScale.SimultaneousFibers

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- Counting the original f-fibers occupied by a refined g-fiber. If g is
determined by f, these original fibers all lie in one original g-fiber. -/
theorem refined_fiber_projection_bound {A B D : Type*} [DecidableEq B] [DecidableEq D]
    (S Q : Finset A) (f : A → B) (g : A → D) (z : D) (q c k : ℕ)
    (hQS : Q ⊆ S)
    (hdet : ∀ x ∈ S, ∀ y ∈ S, f x = f y → g x = g y)
    (hpop : ∀ x ∈ Q, q ≤ c*(S.filter (fun y => f y = f x)).card)
    (hcomp : (S.filter (fun x => g x = z)).card ≤ k*(Q.filter (fun x => g x = z)).card) :
    q*((Q.filter (fun x => g x = z)).image f).card ≤
      c*k*(Q.filter (fun x => g x = z)).card := by
  let Y := (Q.filter (fun x => g x = z)).image f
  have hlow (y) (hy : y ∈ Y) : q ≤ c*(S.filter (fun x => f x = y)).card := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hpop x (Finset.mem_filter.mp hx).1
  have hsub : S.filter (fun x => f x ∈ Y) ⊆ S.filter (fun x => g x = z) := by
    intro x hx
    obtain ⟨hx,hy⟩ := Finset.mem_filter.mp hx
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hy
    obtain ⟨hy,hgz⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hx,(hdet x hx y (hQS hy) he.symm).trans hgz⟩
  have hsum : q*Y.card ≤ c*(S.filter (fun x => g x = z)).card := by
    calc
      _ = ∑ _y ∈ Y, q := by simp [Nat.mul_comm]
      _ ≤ ∑ y ∈ Y, c*(S.filter (fun x => f x = y)).card := Finset.sum_le_sum hlow
      _ = c*(S.filter (fun x => f x ∈ Y)).card := by
        rw [← Finset.mul_sum, Finset.sum_card_fiberwise_eq_card_filter]
      _ ≤ _ := Nat.mul_le_mul_left c (Finset.card_le_card hsub)
  exact hsum.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left c hcomp)

/-- The constructed refinement supplies the projection estimate on EVERY
nonempty final g-fiber, simultaneously for the maps specified by F. -/
theorem exists_refinement_projection_bounds {A B D I J : Type*}
    [DecidableEq A] [DecidableEq D] [DecidableEq J]
    (S R₀ : Finset A) (T : I → Finset B) (f : I → A → B)
    (is : List I) (d : ℕ) (F : Finset J) (g : J → A → D)
    (hR₀ : R₀ ⊆ S) (hf : ∀ i ∈ is, ∀ x ∈ R₀, f i x ∈ T i) :
    ∃ Q ⊆ popularRounds T f d is R₀,
      d*(S.card-Q.card) ≤ 2*d*(S.card-R₀.card)+2*is.length*R₀.card ∧
      ∀ j ∈ F, ∀ i ∈ is,
        (∀ x ∈ S, ∀ y ∈ S, f i x = f i y → g j x = g j y) →
        ∀ z : D, Q.card*((Q.filter (fun x => g j x = z)).image (f i)).card ≤
          (d*(T i).card)*(2*F.card)*(Q.filter (fun x => g j x = z)).card := by
  obtain ⟨Q,hQR,hloss,hcomp,hpop⟩ := exists_popular_stable_refinement S R₀ T f is d F g hR₀ hf
  refine ⟨Q,hQR,hloss,?_⟩
  intro j hj i hi hdet z
  have hQS := hQR.trans ((popularRounds_subset T f d is R₀).trans hR₀)
  by_cases hn : (Q.filter (fun x => g j x = z)).Nonempty
  · obtain ⟨x,hx⟩ := hn
    obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
    apply refined_fiber_projection_bound S Q (f i) (g j) z Q.card (d*(T i).card) (2*F.card) hQS hdet
    · exact fun x hx => hpop i hi x hx
    · simpa only [he] using hcomp j hj x hx
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.refined_fiber_projection_bound
#print axioms KakeyaTwoScale.exists_refinement_projection_bounds
