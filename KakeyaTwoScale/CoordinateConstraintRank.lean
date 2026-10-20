module
public import KakeyaTwoScale.CountableRelativeSard

@[expose] public section

open Set
open scoped ContDiff
noncomputable section
namespace KakeyaTwoScale

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {d : ℕ}

def coordinateConstraint (f : E→F) (g : Fin d→E→ℝ) (J : Finset (Fin d)) :
    E→F×(J→ℝ) := fun x => (f x,fun j => g j x)

theorem coordinateConstraint_contDiff (f : E→F) (g : Fin d→E→ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ∀ j, ContDiff ℝ ∞ (g j)) (J : Finset (Fin d)) :
    ContDiff ℝ ∞ (coordinateConstraint f g J) :=
  hf.prodMk (contDiff_pi.mpr (fun j => hg j))

theorem coordinateConstraint_fderiv (f : E→F) (g : Fin d→E→ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (J : Finset (Fin d)) (x v : E) :
    fderiv ℝ (coordinateConstraint f g J) x v=
      (fderiv ℝ f x v,fun j : J => fderiv ℝ (g j) x v) := by
  have hdf := (hf.differentiable (by simp) x).hasFDerivAt
  have hdg : HasFDerivAt (fun y => fun j : J => g j y)
      (ContinuousLinearMap.pi (fun j : J => fderiv ℝ (g j) x)) x :=
    hasFDerivAt_pi.mpr (fun j => (hg j).differentiable (by simp) x |>.hasFDerivAt)
  have hd : HasFDerivAt (coordinateConstraint f g J)
      ((fderiv ℝ f x).prod (ContinuousLinearMap.pi (fun j : J => fderiv ℝ (g j) x))) x :=
    hdf.prodMk hdg
  rw [hd.fderiv]
  rfl

/-- Appending an actual transverse coordinate raises the constraint rank.
The finite coordinate codomain is constructed, not assumed equivalent to a
product with an extra scalar. -/
theorem coordinateConstraint_insert_range (f : E→F) (g : Fin d→E→ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (J : Finset (Fin d)) (i : Fin d) (x : E)
    (hA : (fderiv ℝ (coordinateConstraint f g J) x).range=⊤)
    (v : E) (hv : fderiv ℝ (coordinateConstraint f g J) x v=0)
    (hvi : fderiv ℝ (g i) x v≠0) :
    (fderiv ℝ (coordinateConstraint f g (insert i J)) x).range=⊤ := by
  classical
  have hh := constraint_pair_surjective
    (fderiv ℝ (coordinateConstraint f g J) x) (fderiv ℝ (g i) x) hA v hv hvi
  apply LinearMap.range_eq_top.mpr
  intro y
  let old : F×(J→ℝ) := (y.1,fun j => y.2 ⟨j,Finset.mem_insert_of_mem j.property⟩)
  obtain ⟨u,hu⟩ := LinearMap.range_eq_top.mp hh (old,y.2 ⟨i,Finset.mem_insert_self _ _⟩)
  have hu1 : fderiv ℝ (coordinateConstraint f g J) x u=old := congrArg Prod.fst hu
  have hu2 : fderiv ℝ (g i) x u=y.2 ⟨i,Finset.mem_insert_self _ _⟩ := congrArg Prod.snd hu
  refine ⟨u,?_⟩
  change fderiv ℝ (coordinateConstraint f g (insert i J)) x u=y
  rw [coordinateConstraint_fderiv f g hf hg]
  apply Prod.ext
  · have hh := congrArg Prod.fst hu1
    rw [coordinateConstraint_fderiv f g hf hg] at hh
    exact hh
  · funext j
    by_cases he : j.val=i
    · have hj : j=⟨i,Finset.mem_insert_self _ _⟩ := Subtype.ext he
      simpa only [hj] using hu2
    · have hj : j.val∈J := (Finset.mem_insert.mp j.property).resolve_left he
      have hold := congrArg (fun p : F×(J→ℝ) => p.2 ⟨j,hj⟩) hu1
      rw [coordinateConstraint_fderiv f g hf hg] at hold
      exact hold

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coordinateConstraint_contDiff
#print axioms KakeyaTwoScale.coordinateConstraint_fderiv
#print axioms KakeyaTwoScale.coordinateConstraint_insert_range
