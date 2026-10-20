module
public import KakeyaTwoScale.ActualVisibilityCoverage
public import KakeyaTwoScale.CubeVisibilityTests

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

abbrev FullCoefficientSphere (N D : ℕ) :=
  sphere (0 : EuclideanSpace ℝ (Fin (Fintype.card (FullDegreeIndex N D)))) 1

def fullCubeVisibilityBody (n D : ℕ) (z : Fin (n+1) → ℝ) (r : ℝ) (hr : 0≤r)
    (hb : ∀ x∈visibilityCube z, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖≤r)
    (ε : ℝ) (p : FullCoefficientSphere (n+1) D) : Set (Fin (n+1) → ℝ) :=
  coordinateVisibilityBody (mollifiedAreaSeminorm (fullDegreeFinMonomial (n+1) D)
    (fullDegreeFinMonomial_injective (n+1) D) (fullDegreeFinMonomial_degree (n+1) D)
    (visibilityCube z) isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr hb ε p)

/-- Complete finite-cube prescribed visibility with inverse-volume targets.
Constants depend only on dimension. Degree precedes the bank and all tests;
one threshold precedes epsilon; the actual full-sphere polynomial comes last. -/
theorem prescribed_cube_visibility (n : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀ (J : ℕ) (z : Fin J → Fin (n+1) → ℝ)
      (M : Fin J → ℝ), (∀ j, 0≤M j) → ∀ (r : ℝ) (hr : 0≤r)
      (hb : ∀ j x, x∈visibilityCube (z j) → ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖≤r),
      ∃ D : ℕ, (D:ℝ)^(n+1)≤K*(∑ j,M j) ∧
      ∃ δ>0, δ<2 ∧ ∀ ε : ℝ, 0<ε → ε≤δ →
        ∃ p : FullCoefficientSphere (n+1) D, ∀ j,
          M j*volume.real (fullCubeVisibilityBody n D (z j) r hr (hb j) ε p)≤1 := by
  classical
  obtain ⟨η,hη,C,hC,hpack⟩ := cube_visibility_test_packing n
  obtain ⟨P,hP,hbanks⟩ := finite_ellipsoid_bank (n+1) (1024*((n+1:ℕ):ℝ)^4) (by positivity)
  let V := visibilityBaseline (n+1)
  have hV : 0<V := visibilityBaseline_pos _
  let K : ℝ := ((n+1:ℕ):ℝ)^(n+1)*(P:ℝ)*(C+V)
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro J z M hM r hr hb
  let L j := visibilitySlotCount C V (M j)
  let count := P*(∑ j,L j)
  obtain ⟨D,hD,hDpow⟩ := full_degree_space_above_count (by omega : 0<n+1) count
  have hcount : (count:ℝ)≤(P:ℝ)*(C+V)*(∑ j,M j) := by
    calc
      (count:ℝ) = (P:ℝ)*(∑ j,(L j:ℝ)) := by simp [count]
      _ ≤ (P:ℝ)*(∑ j,(C+V)*M j) := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun j _ => visibilitySlotCount_bound C V (M j) hC.le hV.le (hM j))) (by positivity)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hdegreeBound : (D:ℝ)^(n+1)≤K*(∑ j,M j) := by
    have hp : (D:ℝ)^(n+1)≤((n+1:ℕ):ℝ)^(n+1)*(count:ℝ) := by exact_mod_cast hDpow
    exact hp.trans (by dsimp [K]; nlinarith [mul_le_mul_of_nonneg_left hcount (by positivity : 0≤((n+1:ℕ):ℝ)^(n+1))])
  let d := Fintype.card (FullDegreeIndex (n+1) D)
  let m := fullDegreeFinMonomial (n+1) D
  have hm : Function.Injective m := fullDegreeFinMonomial_injective _ _
  have hmD : ∀ i, (m i).sum (fun _ e => e)≤D := fullDegreeFinMonomial_degree _ _
  let q := visibilityBankBound n D r
  obtain ⟨F,hF,_,hcover,color,hcolorBound,hcolor⟩ := hbanks (1/4) q (by norm_num)
  let A : ℝ := (4*((n+1:ℕ):ℝ)^2)^(n+1)
  have hA : 0<A := by dsimp [A]; positivity
  let v (B : F) := volume.real (affineEllipsoid B.val 0)
  have hv (B : F) : 0<v B :=
    ENNReal.toReal_pos (affineEllipsoid_positive _ _).ne' (affineEllipsoid_finite _ _).ne
  let W (B : F) := 1/(A*v B)
  have hW (B : F) : 0<W B := one_div_pos.mpr (mul_pos hA (hv B))
  have hWelig (B : F) : 1≤W B*A*v B := by
    dsimp [W]
    field_simp [hA.ne',(hv B).ne']
    exact le_rfl
  choose T hTcard hTinside δ hδ hδ2 hnonbis using
    (fun (j : Fin J) (B : F) => hpack d D m hm hmD q B.val (hF B.property)
      (z j) r hr (hb j) (W B) (hW B) (hWelig B))
  obtain ⟨t,ht,ht2,htall⟩ := finite_positive_threshold
    (fun i : Fin J × F => δ i.1 i.2) (fun i => hδ i.1 i.2)
  let tests j B := if h : B∈F then T j ⟨B,h⟩ else ∅
  have htests (j : Fin J) (B : F) : tests j B.val=T j B := by simp [tests,B.property]
  refine ⟨D,hdegreeBound,t,ht,ht2,?_⟩
  intro ε hε hεt
  have hε2 := hεt.trans_lt ht2
  apply actual_visibility_coverage m hm hmD z r hr hb M hM L hD F color hcolorBound hcolor η hη tests
    ?_ ε hε hε2 ?_ ?_
  · intro j B hBF hactive helig
    let B' : F := ⟨B,hBF⟩
    have hWB : W B'≤M j := by
      apply (div_le_iff₀ (mul_pos hA (hv B'))).mpr
      change 1≤M j*A*v B' at helig
      nlinarith
    have hreal : ((T j B').card:ℝ)≤C*M j :=
      (hTcard j B').trans (mul_le_mul_of_nonneg_left hWB hC.le)
    have hceil : (T j B').card≤⌈C*M j⌉₊ := by
      exact_mod_cast hreal.trans (Nat.le_ceil (C*M j))
    simpa [tests,hBF,L,visibilitySlotCount,show 1<M j*V from hactive] using hceil
  · intro j p
    exact actual_visibility_bank_label m hm hmD (visibilityCube (z j))
      isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr (hb j) F hcover ε hε hε2 p
  · intro j B hBF p hp
    simpa [tests,hBF] using hnonbis j ⟨B,hBF⟩ ε hε (hεt.trans (htall ⟨j,⟨B,hBF⟩⟩)) p hp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.prescribed_cube_visibility
