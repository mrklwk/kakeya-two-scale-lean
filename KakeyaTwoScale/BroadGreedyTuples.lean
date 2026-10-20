module
public import KakeyaTwoScale.BroadSubspaceExtension

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Recursive actual tuple family. The first direction is unrestricted;
each new head has the required normal speed from the span of the tail. -/
def broadGreedyTuples {n N : ℕ} (G : Finset (Fin N))
    (u : Fin N → EuclideanSpace ℝ (Fin n)) (eta : ℝ) :
    (m : ℕ) → Finset (Fin (m+1) → Fin N)
  | 0 => G.image (fun j => fun _ : Fin 1 => j)
  | m+1 => (broadGreedyTuples G u eta m).biUnion (fun f =>
      (G.filter (fun j => eta ≤ ‖normalProjection
        (Submodule.span ℝ (Set.range (fun i => u (f i)))) (u j)‖)).image (fun j => Fin.cons j f))

theorem broadGreedyTuples_mem {n N : ℕ} (G : Finset (Fin N))
    (u : Fin N → EuclideanSpace ℝ (Fin n)) (eta : ℝ) (m : ℕ)
    (f : Fin (m+1) → Fin N) (hf : f ∈ broadGreedyTuples G u eta m) :
    ∀ i, f i∈G := by
  induction m with
  | zero =>
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hf
    exact fun _ => hj
  | succ m ih =>
    obtain ⟨g,hg,hf⟩ := Finset.mem_biUnion.mp hf
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hf
    intro i
    refine Fin.cases ?_ (fun l => ?_) i
    · exact (Finset.mem_filter.mp hj).1
    · exact ih g hg l

theorem broadGreedyTuples_card_zero {n N : ℕ} (G : Finset (Fin N))
    (u : Fin N → EuclideanSpace ℝ (Fin n)) (eta : ℝ) :
    (broadGreedyTuples G u eta 0).card=G.card := by
  apply Finset.card_image_of_injective
  intro j l he
  exact congrFun he 0

theorem broadGreedyTuples_card_succ {n N : ℕ} (G : Finset (Fin N))
    (u : Fin N → EuclideanSpace ℝ (Fin n)) (eta : ℝ) (m : ℕ) :
    (broadGreedyTuples G u eta (m+1)).card =
      ∑ f ∈ broadGreedyTuples G u eta m,
        (G.filter (fun j => eta ≤ ‖normalProjection
          (Submodule.span ℝ (Set.range (fun i => u (f i)))) (u j)‖)).card := by
  rw [broadGreedyTuples,Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro f _
    apply Finset.card_image_of_injective
    intro i j he
    simpa using congrFun he 0
  · intro f _ g _ hfg
    apply Finset.disjoint_left.mpr
    intro v hvf hvg
    obtain ⟨i,hi,hif⟩ := Finset.mem_image.mp hvf
    obtain ⟨j,hj,hjg⟩ := Finset.mem_image.mp hvg
    exact hfg (Fin.cons_inj.mp (hif.trans hjg.symm)).2

/-- Every broad step keeps at least half the original choices. The final
count retains the full first-choice factor, so its rho power is k-1. -/
theorem broadGreedyTuples_card_lower {n N k : ℕ} (G : Finset (Fin N))
    (u : Fin N → EuclideanSpace ℝ (Fin n)) (rho : ℝ)
    (hu : ∀ j∈G, ‖u j‖=1) (hkn : k ≤ n)
    (hbroad : ∀ H : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
      Module.finrank ℝ H=k-1 →
      ((G.filter fun j => planeAngle H (u j)≤rho).card:ℝ)<(G.card:ℝ)/2)
    (m : ℕ) (hm : m+1 ≤ k) :
    (G.card:ℝ)*((G.card:ℝ)/2)^m ≤
      ((broadGreedyTuples G u ((2/Real.pi)*rho) m).card:ℝ) := by
  induction m with
  | zero => simp [broadGreedyTuples_card_zero]
  | succ m ih =>
    have hprev := ih (by omega)
    rw [broadGreedyTuples_card_succ,Nat.cast_sum]
    have hchoices (f : Fin (m+1) → Fin N) : (G.card:ℝ)/2 ≤
        ((G.filter (fun j => (2/Real.pi)*rho ≤ ‖normalProjection
          (Submodule.span ℝ (Set.range (fun i => u (f i)))) (u j)‖)).card:ℝ) := by
      obtain ⟨O,hOG,hO,hs⟩ := broad_prefix_choices G u rho hu (by omega : m+1<k) hkn hbroad f
      apply hO.le.trans
      exact_mod_cast Finset.card_le_card (show O ⊆ G.filter (fun j => _ ) from
        fun j hj => Finset.mem_filter.mpr ⟨hOG hj,(hs j hj).le⟩)
    calc
      _ = ((G.card:ℝ)*((G.card:ℝ)/2)^m)*((G.card:ℝ)/2) := by rw [pow_succ]; ring
      _ ≤ ((broadGreedyTuples G u ((2/Real.pi)*rho) m).card:ℝ)*((G.card:ℝ)/2) :=
        mul_le_mul_of_nonneg_right hprev (by positivity)
      _ = ∑ _f ∈ broadGreedyTuples G u ((2/Real.pi)*rho) m, (G.card:ℝ)/2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun f _ => hchoices f)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.broadGreedyTuples_mem
#print axioms KakeyaTwoScale.broadGreedyTuples_card_zero
#print axioms KakeyaTwoScale.broadGreedyTuples_card_succ
#print axioms KakeyaTwoScale.broadGreedyTuples_card_lower
