module
public import KakeyaTwoScale.LocalOriginalMultiplicity
public import KakeyaTwoScale.BufferedSnapshotAncestry

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace FrozenGeometryState

variable {n k : ℕ} {T C O : Type}

def grainRecords (S : FrozenGeometryState n k T C O) (cube : T→C)
    (g : S.Grain) (j : Fin k) : Finset S.Piece := by
  classical
  exact (S.tuples.filter (fun y=>S.grain (cube y)=g)).image (fun y=>S.parent y j)

theorem grainRecords_subset (S : FrozenGeometryState n k T C O) (cube : T→C)
    (g : S.Grain) (j : Fin k) : S.grainRecords cube g j ⊆ S.records j := by
  classical
  exact Finset.image_subset_image (Finset.filter_subset _ _)

/-- Count full grain records through actual original IDs. No direction
separation is asserted for records, which may repeat the same original. -/
theorem grain_records_le_originals [DecidableEq O]
    (S : FrozenGeometryState n k T C O) (cube : T→C) (tube : T→Fin k→O)
    (δ C0 : ℝ) (hδ : 0<δ) (hC : 0≤C0)
    (b u : O→EuclideanSpace ℝ (Fin n)) (hu : ∀ o, ‖u o‖=1)
    (hcert : BufferedArchiveSnapshot.Certified δ tube (BufferedArchiveSnapshot.ofState S))
    (haxis : ∀ j t, t∈S.records j → S.axis j t=u (S.original j t))
    (hroot : ∀ j t, t∈S.records j → S.geometry δ j t ⊆
      flatCylinder (b (S.original j t)) (u (S.original j t)) 1 δ)
    (hball : ∀ y∈S.tuples, ∀ j, S.geometry δ j (S.parent y j) ⊆
      ball (S.ballCenter (S.grain (cube y))) S.ballRadius)
    (g : S.Grain) (j : Fin k) (hradius : S.ballRadius ≤ C0*S.length δ j) :
    let F := S.grainRecords cube g j
    (F.card:ℝ) ≤ 2*C0*((F.image (S.original j)).card:ℝ) := by
  classical
  let F := S.grainRecords cube g j
  have hF : F ⊆ S.records j := S.grainRecords_subset cube g j
  have hell : 0<S.length δ j := by unfold length; positivity
  have hlocal (t) (ht : t∈F) : S.geometry δ j t ⊆ ball (S.ballCenter g) (C0*S.length δ j) := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
    have hy' := Finset.mem_filter.mp hy
    have hh := hball y hy'.1 j
    rw [hy'.2] at hh
    exact hh.trans (ball_subset_ball hradius)
  have hfiber (o : O) : ((F.filter (fun t=>S.original j t=o)).card:ℝ) ≤ 2*C0 := by
    let G := F.filter (fun t=>S.original j t=o)
    have hdata (t) (ht : t∈G) :
        S.original j t=o ∧ S.axis j t=u o := by
      have hh := Finset.mem_filter.mp ht
      exact ⟨hh.2,(haxis j t (hF hh.1)).trans (congrArg u hh.2)⟩
    apply localized_original_cylinder_card G (b o) (u o) (S.ballCenter g)
      (S.base j) (S.length δ j) 1 δ C0 (hu o) hell hδ hC
    · intro t ht
      have hh := hroot j t (hF (Finset.mem_filter.mp ht).1)
      simpa only [geometry,(hdata t ht).1,(hdata t ht).2] using hh
    · intro t ht
      have hh := hlocal t (Finset.mem_filter.mp ht).1
      simpa only [geometry,(hdata t ht).2] using hh
    · intro t ht v hv htv
      have hh := hcert.2.2.2.2 j o
        ⟨hF (Finset.mem_filter.mp ht).1,(hdata t ht).1⟩
        ⟨hF (Finset.mem_filter.mp hv).1,(hdata v hv).1⟩ htv
      change Disjoint (S.geometry δ j t) (S.geometry δ j v) at hh
      simpa only [geometry,(hdata t ht).2,(hdata v hv).2] using hh
  have hcount := Finset.card_eq_sum_card_fiberwise (s:=F) (t:=F.image (S.original j))
    (f:=S.original j) (fun t ht=>Finset.mem_image_of_mem _ ht)
  have hcountR : (F.card:ℝ)=∑ o∈F.image (S.original j), ((F.filter (fun t=>S.original j t=o)).card:ℝ) := by
    exact_mod_cast hcount
  change (F.card:ℝ) ≤ _
  rw [hcountR]
  calc
    _ ≤ ∑ _o∈F.image (S.original j), 2*C0 := Finset.sum_le_sum (fun o _=>hfiber o)
    _ = _ := by simp [F,mul_comm]

/-- Maximal-family localization gives a dimension/family-only multiplier.
The sum-of-lengths radius bound is the literal normalization output. -/
theorem maximal_family_radius (S : FrozenGeometryState n k T C O)
    (A : ℕ) (δ : ℝ)
    (hradius : S.ballRadius ≤ (A+n+5:ℝ)*δ*(∑ i, (2:ℝ)^(S.height i)))
    (j : Fin k) (hmax : ∀ i, S.length δ i ≤ S.length δ j) :
    S.ballRadius ≤ ((A+n+5:ℝ)*k)*S.length δ j := by
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hmax i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have he : δ*(∑ i, (2:ℝ)^(S.height i))=∑ i, S.length δ i := by
    simp only [Finset.mul_sum,length]
  calc
    S.ballRadius ≤ (A+n+5:ℝ)*(δ*(∑ i, (2:ℝ)^(S.height i))) := by nlinarith [hradius]
    _ = (A+n+5:ℝ)*(∑ i, S.length δ i) := by rw [he]
    _ ≤ (A+n+5:ℝ)*((k:ℝ)*S.length δ j) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.grain_records_le_originals
#print axioms KakeyaTwoScale.FrozenGeometryState.maximal_family_radius
