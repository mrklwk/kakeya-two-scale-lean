module
public import KakeyaTwoScale.ShortenedOverlap

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
variable {X J : Type*} [NormedAddCommGroup X]

/-- A finite projective net chosen FROM the original direction family.
There is no assumed net, maximality certificate, or omitted antipodal case. -/
theorem finite_projective_net (family : Finset J) (a : J → X)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ net : Finset J, net ⊆ family ∧
      (∀ j ∈ net, ∀ k ∈ net, j ≠ k →
        epsilon ≤ dist (a j) (a k) ∧ epsilon ≤ dist (a j) (-a k)) ∧
      (∀ j ∈ family, ∃ k ∈ net, dist (a j) (a k) < epsilon ∨ dist (a j) (-a k) < epsilon) := by
  let separated := fun s : Finset J => ∀ j ∈ s, ∀ k ∈ s, j ≠ k →
    epsilon ≤ dist (a j) (a k) ∧ epsilon ≤ dist (a j) (-a k)
  let candidates := family.powerset.filter separated
  have hempty : (∅ : Finset J) ∈ candidates := by simp [candidates,separated]
  obtain ⟨net,hnet,hmax⟩ := candidates.exists_max_image Finset.card ⟨∅,hempty⟩
  obtain ⟨hsub,hsep⟩ := Finset.mem_filter.mp hnet
  have hsub' : net ⊆ family := Finset.mem_powerset.mp hsub
  refine ⟨net,hsub',hsep,?_⟩
  intro j hj
  by_contra hnone
  have hfar : ∀ k ∈ net, epsilon ≤ dist (a j) (a k) ∧ epsilon ≤ dist (a j) (-a k) := by
    intro k hk
    have hh : ¬ (dist (a j) (a k) < epsilon ∨ dist (a j) (-a k) < epsilon) := by
      intro hc
      exact hnone ⟨k,hk,hc⟩
    exact ⟨le_of_not_gt (fun h => hh (Or.inl h)),le_of_not_gt (fun h => hh (Or.inr h))⟩
  have hjnot : j ∉ net := by
    intro hjn
    have hh := (hfar j hjn).1
    simp only [dist_self] at hh
    linarith
  have hinsert : insert j net ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hj hsub'),?_⟩
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with hxe | hx
    · subst x
      exact hfar y (Finset.mem_of_mem_insert_of_ne hy hxy.symm)
    · rcases Finset.mem_insert.mp hy with hye | hy
      · subst y
        have hh := hfar x hx
        constructor
        · simpa [dist_comm] using hh.1
        · have hs : dist (a x) (-a j) = dist (a j) (-a x) := by
            simp [dist_eq_norm, sub_neg_eq_add, add_comm]
          rw [hs]
          exact hh.2
      · exact hsep x hx y hy hxy
  have hh := hmax (insert j net) hinsert
  rw [Finset.card_insert_of_notMem hjnot] at hh
  omega

/-- Every nonempty original family has a total assignment to the constructed
net, preserving every index and approximating up to sign. -/
theorem finite_projective_net_assignment (family : Finset J) (hne : family.Nonempty)
    (a : J → X) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ (net : Finset J) (assign : J → J), net ⊆ family ∧
      (∀ j ∈ net, ∀ k ∈ net, j ≠ k →
        epsilon ≤ dist (a j) (a k) ∧ epsilon ≤ dist (a j) (-a k)) ∧
      (∀ j ∈ family, assign j ∈ net ∧
        (dist (a j) (a (assign j)) < epsilon ∨ dist (a j) (-a (assign j)) < epsilon)) := by
  obtain ⟨net,hsub,hsep,hcover⟩ := finite_projective_net family a epsilon he
  obtain ⟨j₀,hj₀⟩ := hne
  let assign := fun j => if hj : j ∈ family then Classical.choose (hcover j hj) else j₀
  refine ⟨net,assign,hsub,hsep,?_⟩
  intro j hj
  dsimp [assign]
  rw [dite_eq_left hj]
  exact Classical.choose_spec (hcover j hj)
end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_projective_net
#print axioms KakeyaTwoScale.finite_projective_net_assignment
