module
public import KakeyaTwoScale.EllipsoidNeighborBound
public import KakeyaTwoScale.FiniteConflictColoring

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

/-- Every finite factor-two-separated ellipsoid family has a palette depending
only on dimension and the chosen conflict factor. Distinct R-comparable
ellipsoids receive different colors. The palette precedes the entire family. -/
theorem uniform_ellipsoid_coloring (N : ℕ) (R : ℝ) (hR : 0<R) :
    ∃ M : ℕ, 0<M ∧ ∀ F : Finset ((Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)),
      (∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬ ellipsoidFormComparable 2 A B) →
      ∃ c : ((Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) → ℕ,
        (∀ A ∈ F, c A < M) ∧ ∀ A ∈ F, ∀ B ∈ F,
          A ≠ B → ellipsoidFormComparable R A B → c A ≠ c B := by
  classical
  obtain ⟨M,hM⟩ := ellipsoid_neighbor_bound N R hR
  refine ⟨M+1,by omega,?_⟩
  intro F hsep
  let Rel := fun A B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) =>
    A ≠ B ∧ ellipsoidFormComparable R A B
  have hs : ∀ A B, Rel A B → Rel B A := fun A B h =>
    ⟨h.1.symm,(ellipsoidFormComparable_symm R A B).mp h.2⟩
  have hd : ∀ A ∈ F, (F.filter (Rel A)).card ≤ M := by
    intro A _
    apply hM A
    · intro B hB
      exact (Finset.mem_filter.mp hB).2.2
    · intro B hB C hC hBC
      exact hsep B (Finset.mem_filter.mp hB).1 C (Finset.mem_filter.mp hC).1 hBC
  obtain ⟨c,hc,hproper⟩ := finite_conflict_coloring Rel hs (fun A h => h.1 rfl) M F hd
  exact ⟨c,fun A hA => Nat.lt_succ_of_le (hc A hA),
    fun A hA B hB hAB hcomp => hproper A hA B hB ⟨hAB,hcomp⟩⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_ellipsoid_coloring
