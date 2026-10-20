module
public import KakeyaTwoScale.BoundedFormatSelection

@[expose] public section

open Set MvPolynomial
open OAI.Release061 OAI.Release061.SignElimination
noncomputable section
namespace KakeyaTwoScale

/-- A scalar expression represented by an actual polynomial in the supplied
joint coordinates, before specializing any real parameter. -/
def PolynomialScalar {X ι : Type*} (c : X → ι → ℝ) (f : X → ℝ) : Prop :=
  ∃ p : MvPolynomial ι ℝ, ∀ x, eval (c x) p=f x

namespace PolynomialScalar
variable {X ι : Type*} {c : X → ι → ℝ} {f g : X → ℝ}

theorem coordinate (i : ι) : PolynomialScalar c (fun x => c x i) :=
  ⟨MvPolynomial.X i,fun _ => eval_X _⟩
theorem const (a : ℝ) : PolynomialScalar c (fun _ => a) :=
  ⟨C a,fun _ => eval_C _⟩
theorem add (hf : PolynomialScalar c f) (hg : PolynomialScalar c g) :
    PolynomialScalar c (fun x => f x+g x) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨p+q,fun x => by simp [hp,hq]⟩
theorem sub (hf : PolynomialScalar c f) (hg : PolynomialScalar c g) :
    PolynomialScalar c (fun x => f x-g x) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨p-q,fun x => by simp [hp,hq]⟩
theorem mul (hf : PolynomialScalar c f) (hg : PolynomialScalar c g) :
    PolynomialScalar c (fun x => f x*g x) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨p*q,fun x => by simp [hp,hq]⟩
theorem pow (hf : PolynomialScalar c f) (k : ℕ) :
    PolynomialScalar c (fun x => f x^k) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p^k,fun x => by simp [hp]⟩
theorem sum {α : Type*} (s : Finset α) (F : α → X → ℝ)
    (hF : ∀ j∈s, PolynomialScalar c (F j)) : PolynomialScalar c (fun x => ∑ j∈s,F j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (c := c) 0
  | @insert j s hj ih =>
    simpa [Finset.sum_insert hj] using (hF j (Finset.mem_insert_self _ _)).add
      (ih (fun k hk => hF k (Finset.mem_insert_of_mem hk)))
theorem prod {α : Type*} (s : Finset α) (F : α → X → ℝ)
    (hF : ∀ j∈s, PolynomialScalar c (F j)) : PolynomialScalar c (fun x => ∏ j∈s,F j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (c := c) 1
  | @insert j s hj ih =>
    simpa [Finset.prod_insert hj] using (hF j (Finset.mem_insert_self _ _)).mul
      (ih (fun k hk => hF k (Finset.mem_insert_of_mem hk)))
theorem eq_zero (hf : PolynomialScalar c f) : PolynomialSignSet c {x | f x=0} := by
  obtain ⟨p,hp⟩ := hf
  simpa only [hp] using PolynomialSignSet.zero (c := c) p
theorem lt (hf : PolynomialScalar c f) (hg : PolynomialScalar c g) :
    PolynomialSignSet c {x | f x<g x} := by
  obtain ⟨p,hp⟩ := hg.sub hf
  simpa only [hp,sub_pos] using PolynomialSignSet.positive (c := c) p
theorem le (hf : PolynomialScalar c f) (hg : PolynomialScalar c g) :
    PolynomialSignSet c {x | f x≤g x} := by
  simpa only [compl_ofPred,not_lt] using (hg.lt hf).compl
theorem coordinate_preimage {Y κ : Type*} {d : Y → κ → ℝ}
    (hf : PolynomialScalar c f) (g : Y → X) (r : ι → κ)
    (hc : ∀ y i, c (g y) i=d y (r i)) : PolynomialScalar d (fun y => f (g y)) := by
  obtain ⟨p,hp⟩ := hf
  refine ⟨rename r p,fun y => ?_⟩
  rw [eval_rename]
  have he : d y ∘ r=c (g y) := funext (fun i => (hc y i).symm)
  rw [he,hp]

end PolynomialScalar

/-- Universal real quantification is complement-existential-complement, using
proved real polynomial quantifier elimination, not an additional assumption. -/
theorem polynomialSignSet_forall_real {X ι : Type*} {c : X → ι → ℝ}
    (P : X → ℝ → Prop)
    (hP : PolynomialSignSet (fun z : X × ℝ => fun o : Option ι => o.elim z.2 (c z.1))
      {z | P z.1 z.2}) : PolynomialSignSet c {x | ∀ t, P x t} := by
  have hh := polynomialSignSet_projection_one hP.compl
  convert hh.compl using 1
  ext x
  simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomialSignSet_forall_real
