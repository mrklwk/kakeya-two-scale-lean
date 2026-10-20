module
public import KakeyaTwoScale.FiniteCylinderGridBank
public import KakeyaTwoScale.WedgeBandIntegralAssembly

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace KakeyaTwoScale
open Classical

def rootIncidenceTuples {d k N : ℕ} (delta : ℝ) (cubes : Finset (Fin d→ℤ))
    (F : Finset (Fin k→Fin N)) (T : Fin N→Set (EuclideanSpace ℝ (Fin d))) :
    Finset (RootTuple d k (Fin N)) := by
  classical
  exact (cubes.product F).filter (fun y => ∀j, (rootGridCube delta y.1∩T (y.2 j)).Nonempty)

theorem rootIncidenceTuples_mem {d k N : ℕ} (delta : ℝ) (cubes : Finset (Fin d→ℤ))
    (F : Finset (Fin k→Fin N)) (T : Fin N→Set (EuclideanSpace ℝ (Fin d))) (y) :
    y∈rootIncidenceTuples delta cubes F T ↔
      y.1∈cubes ∧ y.2∈F ∧ ∀j, (rootGridCube delta y.1∩T (y.2 j)).Nonempty := by
  classical
  rcases y with ⟨z,f⟩
  simp only [rootIncidenceTuples,Finset.mem_filter]
  constructor
  · rintro ⟨hm,hi⟩
    exact ⟨(Finset.mem_product.mp hm).1,(Finset.mem_product.mp hm).2,hi⟩
  · rintro ⟨hz,hf,hi⟩
    exact ⟨Finset.mem_product.mpr ⟨hz,hf⟩,hi⟩

theorem rootIncidence_capacity {d k N : ℕ} (delta : ℝ) (cubes : Finset (Fin d→ℤ))
    (F : Finset (Fin k→Fin N)) (T : Fin N→Set (EuclideanSpace ℝ (Fin d)))
    (z : Fin d→ℤ) (hz : z∈cubes) :
    ParentLevel.capacity (rootIncidenceTuples delta cubes F T) Prod.fst z=
      (F.filter (fun f => ∀j, (rootGridCube delta z∩T (f j)).Nonempty)).card := by
  classical
  have he : (rootIncidenceTuples delta cubes F T).filter (fun y => y.1=z)=
      (F.filter (fun f => ∀j, (rootGridCube delta z∩T (f j)).Nonempty)).image (fun f => (z,f)) := by
    ext y
    rcases y with ⟨w,f⟩
    simp only [Finset.mem_filter,rootIncidenceTuples_mem,Finset.mem_image,Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hw,hf,hi⟩,rfl⟩
      exact ⟨f,⟨hf,hi⟩,rfl,rfl⟩
    · rintro ⟨g,⟨hg,hi⟩,rfl,rfl⟩
      exact ⟨⟨hz,hg,hi⟩,rfl⟩
  unfold ParentLevel.capacity
  rw [he,Finset.card_image_of_injective _ (fun f g h => (Prod.mk.inj h).2)]

theorem tuple_indicator_product {X : Type*} {k : ℕ} (T : Fin k→Set X) (x : X) :
    (∏j, (T j).indicator (fun _ => (1:ℝ)) x)=if ∀j, x∈T j then 1 else 0 := by
  classical
  by_cases h : ∀j, x∈T j
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨j,hj⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)

/-- Literal tuple integrands on one cell are bounded by that cell's actual
joint incidence count, with no Cartesian-product enlargement. -/
theorem tuple_sum_le_root_capacity {d k N : ℕ}
    (delta : ℝ) (cubes : Finset (Fin d→ℤ)) (F : Finset (Fin k→Fin N))
    (T : Fin N→Set (EuclideanSpace ℝ (Fin d))) (w : (Fin k→Fin N)→ℝ) (M : ℝ)
    (hM : 0≤M) (hw : ∀f∈F, w f≤M)
    (z : Fin d→ℤ) (hz : z∈cubes) (x) (hx : x∈rootGridCube delta z) :
    (∑f∈F, w f*∏j, (T (f j)).indicator (fun _ => (1:ℝ)) x) ≤
      M*(ParentLevel.capacity (rootIncidenceTuples delta cubes F T) Prod.fst z:ℝ) := by
  classical
  rw [rootIncidence_capacity delta cubes F T z hz]
  have hh : (∑f∈F, w f*∏j, (T (f j)).indicator (fun _ => (1:ℝ)) x) ≤
      ∑f∈F.filter (fun f => ∀j, (rootGridCube delta z∩T (f j)).Nonempty), M := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro f hf
    rw [tuple_indicator_product]
    by_cases ha : ∀j, x∈T (f j)
    · have hi : ∀j, (rootGridCube delta z∩T (f j)).Nonempty := fun j => ⟨x,hx,ha j⟩
      simpa only [ite_eq_left ha,ite_eq_left hi,mul_one] using hw f hf
    · rw [ite_eq_right ha,mul_zero]
      split_ifs
      · exact hM
      · exact le_rfl
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.rootIncidence_capacity
#print axioms KakeyaTwoScale.tuple_sum_le_root_capacity
