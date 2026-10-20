module
public import KakeyaTwoScale.FrozenNormalizationConsequences
public import KakeyaTwoScale.SelectedDegreeFloor
public import KakeyaTwoScale.SeedAssembly

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
namespace KakeyaTwoScale

/-- Exact conversion from the old-grain normalization target to the degree
chosen from the actual new grain count. -/
theorem dimension_stage_target_identity {h h' N P q : ℝ} (hh : 0 < h) (hh' : 0 < h') :
    (N*P/h^q)*h'^(q-1) = N*(P*(h'/h)^q)/h' := by
  rw [Real.rpow_sub hh',Real.rpow_one,Real.div_rpow hh'.le hh.le]
  ring

theorem dimension_stage_degree_identity {h h' d : ℝ}
    (hh : 0 < h) (hh' : 0 < h') (hd : 0 < d) :
    h' = h * ((h'/h)^(1/d))^d := by
  rw [← Real.rpow_mul (div_pos hh' hh).le]
  have he : (1/d)*d=1 := by field_simp
  rw [he,Real.rpow_one]
  field_simp

namespace FrozenGeometryState

/-- Derive the normalized seed upper from actual retained mass, individual
cube-owned grain mass caps, and physical total counts. -/
theorem actual_seed_normalized_count {n k : ℕ} {T C O : Type}
    [DecidableEq T] [DecidableEq C]
    (W S : FrozenGeometryState n k T C O) (cube : T → C) (cubes : Finset C)
    {p q eta capFactor Lambda K : ℝ} (N : Fin k → ℝ) (P : ℝ)
    (hp : 0 < p) (hq : 0 ≤ q) (heta : 0 < eta) (hcapFactor : 0 < capFactor)
    (hLambda : 0 < Lambda) (hK : 0 ≤ K) (hP : 0 ≤ P) (hN : ∀ j, 0 ≤ N j)
    (hWne : W.tuples.Nonempty) (hne : S.tuples.Nonempty)
    (hWmass : 0 < tupleCubeMass W.tuples cube cubes p)
    (hret : eta*tupleCubeMass W.tuples cube cubes p ≤ tupleCubeMass S.tuples cube cubes p)
    (hcap : ∀ g ∈ S.grains cube,
      tupleCubeMass (S.tuples.filter fun y => S.grain (cube y)=g) cube cubes p ≤
        capFactor*tupleCubeMass W.tuples cube cubes p/
          (((W.grains cube).card:ℝ)*Lambda))
    (hcount : ∀ j, (S.count j:ℝ) ≤ K*(N j*P)*Lambda^q) :
    ∀ j, S.normalizedCount cube q j ≤
      (K*(capFactor/eta)^q)*(N j*P/((W.grains cube).card:ℝ)^q) := by
  classical
  let h : ℝ := (W.grains cube).card
  let hs : ℝ := (S.grains cube).card
  have hh : 0 < h := by
    dsimp [h]
    exact_mod_cast Finset.card_pos.mpr (hWne.image (W.grain ∘ cube))
  have hhs : 0 < hs := by
    dsimp [hs]
    exact_mod_cast Finset.card_pos.mpr (hne.image (S.grain ∘ cube))
  have hmass := actual_seed_grain_count S.tuples cube cubes S.grain hp hret hcap
  change eta*tupleCubeMass W.tuples cube cubes p ≤
    hs*(capFactor*tupleCubeMass W.tuples cube cubes p/(h*Lambda)) at hmass
  have hlower : eta*h*Lambda/capFactor ≤ hs := by
    have hx : eta*tupleCubeMass W.tuples cube cubes p*(h*Lambda) ≤
        hs*capFactor*tupleCubeMass W.tuples cube cubes p := by
      apply (le_div_iff₀ (mul_pos hh hLambda)).mp
      convert hmass using 1
      ring
    apply (div_le_iff₀ hcapFactor).mpr
    nlinarith [hWmass]
  have hbase : 0 < eta*h*Lambda/capFactor := by positivity
  have hpow := Real.rpow_le_rpow hbase.le hlower hq
  intro j
  have hnum : 0 ≤ K*(N j*P)*Lambda^q :=
    mul_nonneg (mul_nonneg hK (mul_nonneg (hN j) hP)) (Real.rpow_nonneg hLambda.le q)
  have hh1 : (S.count j:ℝ)/hs^q ≤ (K*(N j*P)*Lambda^q)/(eta*h*Lambda/capFactor)^q :=
    (div_le_div_of_nonneg_right (hcount j) (Real.rpow_nonneg hhs.le q)).trans
      (div_le_div_of_nonneg_left hnum (Real.rpow_pos_of_pos hbase q) hpow)
  have he : (K*(N j*P)*Lambda^q)/(eta*h*Lambda/capFactor)^q =
      (K*(capFactor/eta)^q)*(N j*P/h^q) := by
    rw [Real.div_rpow (by positivity : 0 ≤ eta*h*Lambda) hcapFactor.le,
      Real.mul_rpow (by positivity : 0 ≤ eta*h) hLambda.le,
      Real.mul_rpow heta.le hh.le,Real.div_rpow hcapFactor.le heta.le]
    have hp1 := (Real.rpow_pos_of_pos heta q).ne'
    have hp2 := (Real.rpow_pos_of_pos hh q).ne'
    have hp3 := (Real.rpow_pos_of_pos hLambda q).ne'
    have hp4 := (Real.rpow_pos_of_pos hcapFactor q).ne'
    field_simp
  exact hh1.trans_eq he

/-- A constructed complete dimension-stage normalization, with its targets
expressed in the actual old and final grain cardinalities. The input seed is
concrete; favorable output counts or a successor-existence oracle are not
assumed. The seed-to-archive hypotheses are direct selected-tuple geometry. -/
theorem exists_normalized_dimension_stage {n k A B a dim : ℕ} {T C O : Type}
    [DecidableEq T] [DecidableEq C]
    (W S : FrozenGeometryState n k T C O) (Y₀ : Finset T) (cube : T → C)
    (tube : T → Fin k → O) (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (cubes : Finset C) (center : C → EuclideanSpace ℝ (Fin n))
    {δ p P U eta : ℝ} (N : Fin k → ℝ)
    (hδ : 0 < δ) (hp : 0 < p) (hp1 : p ≤ 1) (hdim : 0 < dim) (ha : 0 < a)
    (hP : 0 ≤ P) (hN : ∀ j, 0 ≤ N j)
    (hv : S.Valid Y₀ cube tube Q δ) (hb : S.Balanced cube cubes p)
    (hne : S.tuples.Nonempty) (hcubes : ∀ y ∈ Y₀, cube y ∈ cubes)
    (hbound : (Y₀.card:ℝ) ≤ (2:ℝ)^B)
    (hQ : ∀ c ∈ cubes, ∀ x ∈ Q c, dist x (center c) ≤ (A:ℝ)*δ)
    (hscale : S.ballRadius ≤ (A+n+5:ℝ)*δ*(∑ j, (2:ℝ)^(S.height j)))
    (hWb : W.Balanced cube cubes p) (hWmass : 0 < tupleCubeMass W.tuples cube cubes p)
    (hSW : S.tuples ⊆ W.tuples)
    (seedLift : S.Grain → W.Grain)
    (hseedLift : ∀ y ∈ S.tuples, seedLift (S.grain (cube y))=W.grain (cube y))
    (hseedGeom : ∀ y ∈ S.tuples, ∀ j,
      S.geometry δ j (S.parent y j) ⊆ W.geometry δ j (W.parent y j))
    (hseedAxis : ∀ y ∈ S.tuples, ∀ j,
      S.axis j (S.parent y j)=W.axis j (W.parent y j))
    (hseedMass : eta*tupleCubeMass W.tuples cube cubes p ≤ tupleCubeMass S.tuples cube cubes p)
    (hseedCount : ∀ j, S.normalizedCount cube (1/(dim:ℝ)) j ≤
      U*(N j*P/((W.grains cube).card:ℝ)^(1/(dim:ℝ)))) :
    ∃ (R : ℕ) (V : FrozenGeometryState n k T C O),
      let D : ℝ := (((V.grains cube).card:ℝ)/(W.grains cube).card)^(1/(dim:ℝ))
      let L : ℝ := ((3^k*(2*(A+n+5)+1)^n*(B+1)^(k+1):ℕ):ℝ)
      V.Valid Y₀ cube tube Q δ ∧ V.Balanced cube cubes p ∧ V.tuples.Nonempty ∧
      V.tuples ⊆ S.tuples ∧ V.tuples ⊆ W.tuples ∧
      0 < D ∧ ((V.grains cube).card:ℝ)=((W.grains cube).card:ℝ)*D^(dim:ℝ) ∧
      R*a ≤ frozenHeightPotential a S.height ∧ (∀ j, V.height j ≤ S.height j) ∧
      V.ballRadius ≤ (A+n+5:ℝ)*δ*(∑ j, (2:ℝ)^(V.height j)) ∧
      eta/L^R*tupleCubeMass W.tuples cube cubes p ≤ tupleCubeMass V.tuples cube cubes p ∧
      eta/L^R*((W.grains cube).card:ℝ) ≤ 2*((V.grains cube).card:ℝ) ∧
      (∀ g ∈ V.grains cube, ∀ j,
        (grainRecordCount V.tuples cube V.grain (fun y => V.parent y j) g:ℝ) ≤
          ((2:ℝ)^(R+1)*max U ((2:ℝ)^(a+1))) *
            (N j*(P*D)/((V.grains cube).card:ℝ))) ∧
      (∀ g ∈ V.grains cube, ∀ j, 0 < V.height j →
        N j*(P*D)/((V.grains cube).card:ℝ) ≤
          (grainRecordCount V.tuples cube V.grain (fun y => V.parent y j) g:ℝ)) ∧
      (∀ y ∈ V.tuples, ∀ j,
        V.geometry δ j (V.parent y j) ⊆ S.geometry δ j (S.parent y j)) ∧
      (∀ y ∈ V.tuples, ∀ j,
        V.geometry δ j (V.parent y j) ⊆ W.geometry δ j (W.parent y j)) ∧
      (∀ y ∈ V.tuples, ∀ j, V.axis j (V.parent y j)=W.axis j (W.parent y j)) ∧
      (∃ lift : V.Grain → W.Grain, ∀ y ∈ V.tuples,
        lift (V.grain (cube y))=W.grain (cube y)) := by
  classical
  let q : ℝ := 1/(dim:ℝ)
  let h : ℝ := (W.grains cube).card
  have hWne : W.tuples.Nonempty := hne.mono hSW
  have hh : 0 < h := by
    dsimp [h]
    exact_mod_cast Finset.card_pos.mpr (hWne.image _)
  have hdimR : (0:ℝ) < dim := by exact_mod_cast hdim
  have hq : 0 ≤ q := (div_pos zero_lt_one hdimR).le
  have hq1 : q ≤ 1 := by
    dsimp [q]
    apply (div_le_iff₀ hdimR).mpr
    exact_mod_cast (by omega : 1 ≤ 1*dim)
  let beta : Fin k → ℝ := fun j => N j*P/h^q
  have hbeta : ∀ j, 0 ≤ beta j := fun j => div_nonneg (mul_nonneg (hN j) hP) (Real.rpow_nonneg hh.le q)
  obtain ⟨R,V,hVv,hVb,hVne,hVS,hVlower,hR,hheight,hball,hmass,hcounts,hgeom,haxis,lift,hLift⟩ :=
    exists_frozen_normalization S Y₀ cube tube Q cubes center hδ hp hp1 hq hq1 ha
      hv hb hne hcubes hbound hQ beta hbeta hscale
  let h' : ℝ := (V.grains cube).card
  have hh' : 0 < h' := by
    dsimp [h']
    exact_mod_cast Finset.card_pos.mpr (hVne.image _)
  let D : ℝ := (h'/h)^q
  let L : ℝ := ((3^k*(2*(A+n+5)+1)^n*(B+1)^(k+1):ℕ):ℝ)
  have hL : 0 < L := by dsimp [L]; positivity
  have hret : eta/L^R*tupleCubeMass W.tuples cube cubes p ≤ tupleCubeMass V.tuples cube cubes p := by
    have hr := (div_le_div_of_nonneg_right hseedMass (pow_nonneg hL.le R)).trans hmass
    convert hr using 1
    dsimp [L]
    ring
  have hfloor : eta/L^R*h ≤ 2*h' := by
    exact selected_child_card_survival W.tuples V.tuples cube cubes W.grain V.grain
      (seedLift ∘ lift) (hVS.trans hSW)
      (fun y hy => (congrArg seedLift (hLift y hy)).trans (hseedLift y (hVS hy)))
      hp (by norm_num) hWmass hret (fun g hg => (hWb g hg).1.2)
  have htarget (j) : beta j*h'^(q-1)=N j*(P*D)/h' :=
    dimension_stage_target_identity hh hh'
  have hupper (j) : (V.count j:ℝ) ≤
      ((2:ℝ)^R*max U ((2:ℝ)^(a+1)))*beta j*h'^q := by
    have hs : S.normalizedCount cube q j ≤ U*beta j := hseedCount j
    have hm : max (S.normalizedCount cube q j) (beta j*(2:ℝ)^(a+1)) ≤
        max U ((2:ℝ)^(a+1))*beta j := by
      apply max_le
      · exact hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hbeta j))
      · simpa only [mul_comm] using
          mul_le_mul_of_nonneg_right (le_max_right U ((2:ℝ)^(a+1))) (hbeta j)
    have hc := (hcounts j).trans (mul_le_mul_of_nonneg_left hm (by positivity))
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hh' q)).mp (by
      simpa only [normalizedCount,mul_assoc] using hc)
  refine ⟨R,V,hVv,hVb,hVne,hVS,hVS.trans hSW,
    Real.rpow_pos_of_pos (div_pos hh' hh) q,
    dimension_stage_degree_identity hh hh' hdimR,hR,hheight,hball,hret,hfloor,?_,?_,hgeom,?_,?_,?_⟩
  · intro g hg j
    have hc := (hVb g hg).2 j |>.2
    have hu := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hupper j) (by norm_num : (0:ℝ)≤2)) hh'.le
    have he : 2*(((2:ℝ)^R*max U ((2:ℝ)^(a+1)))*beta j*h'^q)/h' =
        ((2:ℝ)^(R+1)*max U ((2:ℝ)^(a+1)))*(N j*(P*D)/h') := by
      rw [← htarget j,Real.rpow_sub hh',Real.rpow_one,pow_succ]
      ring
    exact hc.trans (hu.trans_eq he)
  · intro g hg j hj
    rw [← htarget j]
    exact active_grain_lower_count V cube cubes beta hVne hVb hVlower hg j hj
  · intro y hy j
    exact (hgeom y hy j).trans (hseedGeom y (hVS hy) j)
  · intro y hy j
    exact (haxis y hy j).trans (hseedAxis y (hVS hy) j)
  · exact ⟨seedLift ∘ lift,fun y hy =>
      (congrArg seedLift (hLift y hy)).trans (hseedLift y (hVS hy))⟩

/-- Complete actual normalization with its seed upper derived from mass caps
and physical record counts, rather than supplied in normalized units. -/
theorem exists_normalized_dimension_stage_of_mass_caps {n k A B a dim : ℕ} {T C O : Type}
    [DecidableEq T] [DecidableEq C]
    (W S : FrozenGeometryState n k T C O) (Y₀ : Finset T) (cube : T → C)
    (tube : T → Fin k → O) (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (cubes : Finset C) (center : C → EuclideanSpace ℝ (Fin n))
    {δ p P eta capFactor Lambda K : ℝ} (N : Fin k → ℝ)
    (hδ : 0 < δ) (hp : 0 < p) (hp1 : p ≤ 1) (hdim : 0 < dim) (ha : 0 < a)
    (hP : 0 ≤ P) (hN : ∀ j, 0 ≤ N j)
    (hv : S.Valid Y₀ cube tube Q δ) (hb : S.Balanced cube cubes p)
    (hne : S.tuples.Nonempty) (hcubes : ∀ y ∈ Y₀, cube y ∈ cubes)
    (hbound : (Y₀.card:ℝ) ≤ (2:ℝ)^B)
    (hQ : ∀ c ∈ cubes, ∀ x ∈ Q c, dist x (center c) ≤ (A:ℝ)*δ)
    (hscale : S.ballRadius ≤ (A+n+5:ℝ)*δ*(∑ j, (2:ℝ)^(S.height j)))
    (hWb : W.Balanced cube cubes p) (hWmass : 0 < tupleCubeMass W.tuples cube cubes p)
    (hSW : S.tuples ⊆ W.tuples)
    (seedLift : S.Grain → W.Grain)
    (hseedLift : ∀ y ∈ S.tuples, seedLift (S.grain (cube y))=W.grain (cube y))
    (hseedGeom : ∀ y ∈ S.tuples, ∀ j,
      S.geometry δ j (S.parent y j) ⊆ W.geometry δ j (W.parent y j))
    (hseedAxis : ∀ y ∈ S.tuples, ∀ j,
      S.axis j (S.parent y j)=W.axis j (W.parent y j))
    (hseedMass : eta*tupleCubeMass W.tuples cube cubes p ≤ tupleCubeMass S.tuples cube cubes p)
    (heta : 0 < eta) (hcapFactor : 0 < capFactor) (hLambda : 0 < Lambda) (hK : 0 ≤ K)
    (hcap : ∀ g ∈ S.grains cube,
      tupleCubeMass (S.tuples.filter fun y => S.grain (cube y)=g) cube cubes p ≤
        capFactor*tupleCubeMass W.tuples cube cubes p/
          (((W.grains cube).card:ℝ)*Lambda))
    (hcount : ∀ j, (S.count j:ℝ) ≤ K*(N j*P)*Lambda^(1/(dim:ℝ))) :
    ∃ (R : ℕ) (V : FrozenGeometryState n k T C O),
      let D : ℝ := (((V.grains cube).card:ℝ)/(W.grains cube).card)^(1/(dim:ℝ))
      let L : ℝ := ((3^k*(2*(A+n+5)+1)^n*(B+1)^(k+1):ℕ):ℝ)
      V.Valid Y₀ cube tube Q δ ∧ V.Balanced cube cubes p ∧ V.tuples.Nonempty ∧
      V.tuples ⊆ S.tuples ∧ V.tuples ⊆ W.tuples ∧
      0 < D ∧ ((V.grains cube).card:ℝ)=((W.grains cube).card:ℝ)*D^(dim:ℝ) ∧
      R*a ≤ frozenHeightPotential a S.height ∧ (∀ j, V.height j ≤ S.height j) ∧
      V.ballRadius ≤ (A+n+5:ℝ)*δ*(∑ j, (2:ℝ)^(V.height j)) ∧
      eta/L^R*tupleCubeMass W.tuples cube cubes p ≤ tupleCubeMass V.tuples cube cubes p ∧
      eta/L^R*((W.grains cube).card:ℝ) ≤ 2*((V.grains cube).card:ℝ) ∧
      (∀ g ∈ V.grains cube, ∀ j,
        (grainRecordCount V.tuples cube V.grain (fun y => V.parent y j) g:ℝ) ≤
          ((2:ℝ)^(R+1)*max (K*(capFactor/eta)^(1/(dim:ℝ))) ((2:ℝ)^(a+1))) *
            (N j*(P*D)/((V.grains cube).card:ℝ))) ∧
      (∀ g ∈ V.grains cube, ∀ j, 0 < V.height j →
        N j*(P*D)/((V.grains cube).card:ℝ) ≤
          (grainRecordCount V.tuples cube V.grain (fun y => V.parent y j) g:ℝ)) ∧
      (∀ y ∈ V.tuples, ∀ j,
        V.geometry δ j (V.parent y j) ⊆ S.geometry δ j (S.parent y j)) ∧
      (∀ y ∈ V.tuples, ∀ j,
        V.geometry δ j (V.parent y j) ⊆ W.geometry δ j (W.parent y j)) ∧
      (∀ y ∈ V.tuples, ∀ j, V.axis j (V.parent y j)=W.axis j (W.parent y j)) ∧
      (∃ lift : V.Grain → W.Grain, ∀ y ∈ V.tuples,
        lift (V.grain (cube y))=W.grain (cube y)) := by
  have hq : 0 ≤ (1/(dim:ℝ)) := by positivity
  have hc := actual_seed_normalized_count W S cube cubes N P hp hq heta hcapFactor
    hLambda hK hP hN (hne.mono hSW) hne hWmass hseedMass hcap hcount
  exact exists_normalized_dimension_stage W S Y₀ cube tube Q cubes center N hδ hp hp1
    hdim ha hP hN hv hb hne hcubes hbound hQ hscale hWb hWmass hSW seedLift
    hseedLift hseedGeom hseedAxis hseedMass hc


end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.dimension_stage_target_identity
#print axioms KakeyaTwoScale.dimension_stage_degree_identity
#print axioms KakeyaTwoScale.FrozenGeometryState.exists_normalized_dimension_stage

#print axioms KakeyaTwoScale.FrozenGeometryState.actual_seed_normalized_count
#print axioms KakeyaTwoScale.FrozenGeometryState.exists_normalized_dimension_stage_of_mass_caps
