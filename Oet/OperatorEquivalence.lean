import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.Topology.Instances.Matrix

set_option linter.style.header false

namespace OET

open Matrix Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §1  Reservoir model and eigenstructure of the exchange operator `A` -/

/-- Eigenstructure of the linear exchange operator `A`.
Column `j` of `V` is the right eigenvector `v_j`; column `j` of `W` is the left
eigenvector `w_j`; `lam j` is the eigenvalue `λ_j`. The field `biorth` is
`w_jᵀ v_k = δ_jk`. -/
structure EigenData (A : Matrix ι ι ℝ) where
  lam : ι → ℝ
  V : Matrix ι ι ℝ
  W : Matrix ι ι ℝ
  right : A * V = V * diagonal lam
  left : Wᵀ * A = diagonal lam * Wᵀ
  biorth : Wᵀ * V = 1

/-- The atmospheric unit vector `e_a`. -/
def ea (a : ι) : ι → ℝ := Pi.single a 1

namespace EigenData

variable {A : Matrix ι ι ℝ} (E : EigenData A)

/-- The right eigenvector `v_j` (column `j` of `V`). -/
def rv (j : ι) : ι → ℝ := fun i => E.V i j

/-- The atmospheric visibility product `(w_jᵀ e_a) v_{j,a}`. -/
def visibility (a j : ι) : ℝ := E.W a j * E.V a j

/-- `w_jᵀ e_a = W a j`. -/
theorem left_dot_ea (a j : ι) : (E.Wᵀ *ᵥ ea a) j = E.W a j := by
  simp [ea, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Completeness of the eigenbasis: `V Wᵀ = 1`, from `Wᵀ V = 1` for square matrices. -/
theorem complete : E.V * E.Wᵀ = 1 := mul_eq_one_comm.mp E.biorth

/-- Every vector equals its expansion in the right eigenbasis:
`x = Σ_j (w_jᵀ x) v_j`, written as `V (Wᵀ x) = x`. -/
theorem reconstruct (x : ι → ℝ) : E.V *ᵥ (E.Wᵀ *ᵥ x) = x := by
  rw [mulVec_mulVec, E.complete, one_mulVec]

/-- Proof step 1: `e_a = Σ_j (w_jᵀ e_a) v_j`. -/
theorem atm_eigen_expansion (a : ι) :
    ea a = ∑ j, E.W a j • E.rv j := by
  have h : E.Wᵀ *ᵥ ea a = fun j => E.W a j := funext (E.left_dot_ea a)
  conv_lhs => rw [← E.reconstruct (ea a), h]
  ext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rv]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/-! ## §2  The `−λ₁₄ I` shift leaves the eigenvectors unchanged -/

/-- Right eigenvectors of `A − c I` are those of `A`, with eigenvalues `λ_j − c`. -/
theorem eigen_shift_right (c : ℝ) :
    (A - c • (1 : Matrix ι ι ℝ)) * E.V = E.V * diagonal (fun j => E.lam j - c) := by
  rw [sub_mul, Matrix.smul_mul, one_mul, E.right]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul]
  ring

/-- Left eigenvectors of `A − c I` are those of `A`, with eigenvalues `λ_j − c`. -/
theorem eigen_shift_left (c : ℝ) :
    E.Wᵀ * (A - c • (1 : Matrix ι ι ℝ)) = diagonal (fun j => E.lam j - c) * E.Wᵀ := by
  rw [mul_sub, Matrix.mul_smul, mul_one, E.left]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_mul, smul_eq_mul]
  ring

/-! ## §3  Modal solution of a linear system sharing the eigenvectors of `A` -/

/-- If `Wᵀ B = diag(μ) Wᵀ` and `x' = B x` for `t ≥ 0`, then every modal coordinate
evolves as `(w_jᵀ x)(t) = (w_jᵀ x)(0) e^{μ_j t}`. -/
theorem modal_evolution (B : Matrix ι ι ℝ) (μ : ι → ℝ)
    (hB : E.Wᵀ * B = diagonal μ * E.Wᵀ)
    (x : ℝ → ι → ℝ) (hcont : ContinuousOn x (Ici 0))
    (hode : ∀ t, 0 ≤ t → HasDerivWithinAt x (B *ᵥ x t) (Ici t) t)
    (j : ι) (t : ℝ) (ht : 0 ≤ t) :
    (E.Wᵀ *ᵥ x t) j = (E.Wᵀ *ᵥ x 0) j * Real.exp (μ j * t) := by
  -- the modal coordinate `y(s) = (w_jᵀ x)(s)` satisfies `y' = μ_j y`
  have hy : ∀ s, 0 ≤ s →
      HasDerivWithinAt (fun r => (E.Wᵀ *ᵥ x r) j) (μ j * (E.Wᵀ *ᵥ x s) j) (Ici s) s := by
    intro s hs
    have hc := hasDerivWithinAt_pi.1 (hode s hs)
    have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ)
      (fun i _ => (hc i).const_mul (E.Wᵀ j i))
    have hval : (E.Wᵀ *ᵥ (B *ᵥ x s)) j = μ j * (E.Wᵀ *ᵥ x s) j := by
      rw [mulVec_mulVec, hB, ← mulVec_mulVec, mulVec_diagonal]
    rw [← hval]
    simpa only [Matrix.mulVec, dotProduct] using hsum
  -- `g(s) = y(s) e^{-μ_j s}` has zero right derivative
  have hg : ∀ s, 0 ≤ s → HasDerivWithinAt
      (fun r => (E.Wᵀ *ᵥ x r) j * Real.exp (-μ j * r)) 0 (Ici s) s := by
    intro s hs
    have he : HasDerivAt (fun r => Real.exp (-μ j * r)) (Real.exp (-μ j * s) * (-μ j)) s := by
      simpa using ((hasDerivAt_id s).const_mul (-μ j)).exp
    exact ((hy s hs).mul he.hasDerivWithinAt).congr_deriv (by ring)
  have hgc : ContinuousOn (fun r => (E.Wᵀ *ᵥ x r) j * Real.exp (-μ j * r)) (Ici 0) := by
    have hL : Continuous (fun v : ι → ℝ => E.Wᵀ *ᵥ v) :=
      continuous_const.matrix_mulVec continuous_id
    have h1 : ContinuousOn (fun r => (E.Wᵀ *ᵥ x r) j) (Ici 0) :=
      (continuous_apply j).comp_continuousOn (hL.comp_continuousOn hcont)
    have h2 : Continuous (fun r : ℝ => Real.exp (-μ j * r)) := by fun_prop
    exact h1.mul h2.continuousOn
  have hconst := constant_of_has_deriv_right_zero (a := 0) (b := t)
    (hgc.mono Icc_subset_Ici_self) (fun s hs => hg s hs.1) t ⟨ht, le_rfl⟩
  simp only [mul_zero, Real.exp_zero, mul_one] at hconst
  calc (E.Wᵀ *ᵥ x t) j
      = (E.Wᵀ *ᵥ x t) j * Real.exp (-μ j * t) * Real.exp (μ j * t) := by
        rw [mul_assoc, ← Real.exp_add, show -μ j * t + μ j * t = 0 by ring,
          Real.exp_zero, mul_one]
    _ = (E.Wᵀ *ᵥ x 0) j * Real.exp (μ j * t) := by rw [hconst]

/-- Full modal solution: `x(t) = Σ_j (w_jᵀ x(0)) e^{μ_j t} v_j` for `t ≥ 0`. -/
theorem modal_solution (B : Matrix ι ι ℝ) (μ : ι → ℝ)
    (hB : E.Wᵀ * B = diagonal μ * E.Wᵀ)
    (x : ℝ → ι → ℝ) (hcont : ContinuousOn x (Ici 0))
    (hode : ∀ t, 0 ≤ t → HasDerivWithinAt x (B *ᵥ x t) (Ici t) t)
    (t : ℝ) (ht : 0 ≤ t) :
    x t = ∑ j, ((E.Wᵀ *ᵥ x 0) j * Real.exp (μ j * t)) • E.rv j := by
  have hm : E.Wᵀ *ᵥ x t = fun j => (E.Wᵀ *ᵥ x 0) j * Real.exp (μ j * t) :=
    funext fun j => E.modal_evolution B μ hB x hcont hode j t ht
  conv_lhs => rw [← E.reconstruct (x t), hm]
  ext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rv]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/-! ## §4  Operator-Equivalence Theorem (Appendix A.2) -/

/-- Bomb-¹⁴C content response, eq. (68) with `δX(0) = α e_a` and no subsequent source:
`δX(t) = α Σ_j (w_jᵀ e_a) e^{(λ_j − λ₁₄) t} v_j`. -/
theorem bomb14c_solution (a : ι) (lam14 α : ℝ) (δX : ℝ → ι → ℝ)
    (hcont : ContinuousOn δX (Ici 0))
    (hode : ∀ t, 0 ≤ t →
      HasDerivWithinAt δX ((A - lam14 • (1 : Matrix ι ι ℝ)) *ᵥ δX t) (Ici t) t)
    (hinit : δX 0 = α • ea a) (t : ℝ) (ht : 0 ≤ t) :
    δX t = ∑ j, (α * E.W a j * Real.exp ((E.lam j - lam14) * t)) • E.rv j := by
  rw [E.modal_solution _ (fun j => E.lam j - lam14) (E.eigen_shift_left lam14) δX hcont hode
    t ht, hinit, mulVec_smul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.smul_apply, E.left_dot_ea, smul_eq_mul]

/-- Mass response to an atmospheric emission impulse `δe(t) = β e_a δ(t)`, eq. (67).
The impulse is encoded by its Duhamel solution: `δM(0⁺) = β e_a` and `δM' = A δM`
for `t ≥ 0`. Then `δM(t) = β Σ_j (w_jᵀ e_a) e^{λ_j t} v_j`. -/
theorem mass_impulse_solution (a : ι) (β : ℝ) (δM : ℝ → ι → ℝ)
    (hcont : ContinuousOn δM (Ici 0))
    (hode : ∀ t, 0 ≤ t → HasDerivWithinAt δM (A *ᵥ δM t) (Ici t) t)
    (hinit : δM 0 = β • ea a) (t : ℝ) (ht : 0 ≤ t) :
    δM t = ∑ j, (β * E.W a j * Real.exp (E.lam j * t)) • E.rv j := by
  rw [E.modal_solution A E.lam E.left δM hcont hode t ht, hinit, mulVec_smul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.smul_apply, E.left_dot_ea, smul_eq_mul]

/-- Eq. (69): atmospheric component of the bomb-¹⁴C content response,
`δX_a(t) = Σ_j α (w_jᵀ e_a) v_{j,a} e^{(λ_j − λ₁₄) t}`. -/
theorem bomb14c_atm (a : ι) (lam14 α : ℝ) (δX : ℝ → ι → ℝ)
    (hcont : ContinuousOn δX (Ici 0))
    (hode : ∀ t, 0 ≤ t →
      HasDerivWithinAt δX ((A - lam14 • (1 : Matrix ι ι ℝ)) *ᵥ δX t) (Ici t) t)
    (hinit : δX 0 = α • ea a) (t : ℝ) (ht : 0 ≤ t) :
    δX t a = ∑ j, α * E.visibility a j * Real.exp ((E.lam j - lam14) * t) := by
  rw [E.bomb14c_solution a lam14 α δX hcont hode hinit t ht]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rv, visibility]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- Eq. (70): atmospheric component of the mass impulse response,
`δM_a(t) = Σ_j β (w_jᵀ e_a) v_{j,a} e^{λ_j t}`. -/
theorem mass_atm (a : ι) (β : ℝ) (δM : ℝ → ι → ℝ)
    (hcont : ContinuousOn δM (Ici 0))
    (hode : ∀ t, 0 ≤ t → HasDerivWithinAt δM (A *ᵥ δM t) (Ici t) t)
    (hinit : δM 0 = β • ea a) (t : ℝ) (ht : 0 ≤ t) :
    δM t a = ∑ j, β * E.visibility a j * Real.exp (E.lam j * t) := by
  rw [E.mass_impulse_solution a β δM hcont hode hinit t ht]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rv, visibility]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- **Operator-Equivalence Theorem** (Appendix A.2, eqs. (69) and (70)).
Under hypotheses (i)–(iii), the atmospheric expression of mode `j` is
`α (w_jᵀ e_a) v_{j,a} e^{(λ_j − λ₁₄) t}` in the bomb-¹⁴C response and
`β (w_jᵀ e_a) v_{j,a} e^{λ_j t}` in the mass response. The atmospheric
visibility product `(w_jᵀ e_a) v_{j,a}` (`E.visibility a j`) is the same in both. -/
theorem operator_equivalence (a : ι) (lam14 α β : ℝ)
    (δX δM : ℝ → ι → ℝ)
    (hXc : ContinuousOn δX (Ici 0))
    (hXode : ∀ t, 0 ≤ t →
      HasDerivWithinAt δX ((A - lam14 • (1 : Matrix ι ι ℝ)) *ᵥ δX t) (Ici t) t)
    (hXinit : δX 0 = α • ea a)
    (hMc : ContinuousOn δM (Ici 0))
    (hModeq : ∀ t, 0 ≤ t → HasDerivWithinAt δM (A *ᵥ δM t) (Ici t) t)
    (hMinit : δM 0 = β • ea a)
    (t : ℝ) (ht : 0 ≤ t) :
    δX t a = ∑ j, α * E.visibility a j * Real.exp ((E.lam j - lam14) * t) ∧
    δM t a = ∑ j, β * E.visibility a j * Real.exp (E.lam j * t) :=
  ⟨E.bomb14c_atm a lam14 α δX hXc hXode hXinit t ht,
    E.mass_atm a β δM hMc hModeq hMinit t ht⟩

/-- Hypothesis (iv): the observed atmospheric ratio anomaly is proportional to `δX_a`.
Then `δR_a` carries mode `j` with the same visibility product `(w_jᵀ e_a) v_{j,a}`. -/
theorem observed_ratio_modes (a : ι) (lam14 α κ : ℝ)
    (δX : ℝ → ι → ℝ) (δRa : ℝ → ℝ)
    (hXc : ContinuousOn δX (Ici 0))
    (hXode : ∀ t, 0 ≤ t →
      HasDerivWithinAt δX ((A - lam14 • (1 : Matrix ι ι ℝ)) *ᵥ δX t) (Ici t) t)
    (hXinit : δX 0 = α • ea a)
    (hiv : ∀ t, 0 ≤ t → δRa t = κ * δX t a)
    (t : ℝ) (ht : 0 ≤ t) :
    δRa t = ∑ j, κ * α * E.visibility a j * Real.exp ((E.lam j - lam14) * t) := by
  rw [hiv t ht, E.bomb14c_atm a lam14 α δX hXc hXode hXinit t ht, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

end EigenData

end OET

#print axioms OET.EigenData.operator_equivalence
#print axioms OET.EigenData.observed_ratio_modes
