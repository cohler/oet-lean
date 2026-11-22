# Paper ↔ Lean Correspondence

**Paper:** Cohler, J. and Soon, W. *Bomb-Radiocarbon Decay Falsifies the IPCC (Part II).*
Appendix A.2, Operator-Equivalence Theorem. The exact version this file
documents is [`paper/bomb14c-scc-part2.pdf`](paper/bomb14c-scc-part2.pdf)
in this repository.
**Formalization:** this repository, file `Oet/OperatorEquivalence.lean`.

Each item in Appendix A.2 maps to the Lean declaration named below.
Every mapping can be audited by comparing the paper's statement to the
cited Lean line. Line links open the Lean source in the same version of
this repository you are viewing.

## Reservoir model and eigenstructure

| Paper                                              | Lean declaration                 | Line |
|----------------------------------------------------|----------------------------------|------|
| Reservoir index set (atmosphere + `N − 1` reservoirs) | `ι : Type*` with `[Fintype ι]` | n/a  |
| Linear exchange operator `A`                       | `A : Matrix ι ι ℝ`               | [21](Oet/OperatorEquivalence.lean#L21) |
| Eigenvalues `{λ_j}`                                | `EigenData.lam`                  | [22](Oet/OperatorEquivalence.lean#L22) |
| Right eigenvectors `{v_j}` (columns of `V`)        | `EigenData.V`, `rv`              | [23](Oet/OperatorEquivalence.lean#L23), [37](Oet/OperatorEquivalence.lean#L37) |
| Left eigenvectors `{w_j}` (columns of `W`)         | `EigenData.W`                    | [24](Oet/OperatorEquivalence.lean#L24) |
| `A v_j = λ_j v_j`                                  | `EigenData.right`                | [25](Oet/OperatorEquivalence.lean#L25) |
| `w_jᵀ A = λ_j w_jᵀ`                                | `EigenData.left`                 | [26](Oet/OperatorEquivalence.lean#L26) |
| `w_jᵀ v_k = δ_jk`                                  | `EigenData.biorth`               | [27](Oet/OperatorEquivalence.lean#L27) |
| Atmospheric unit vector `e_a`                      | `ea`                             | [30](Oet/OperatorEquivalence.lean#L30) |
| Visibility product `(w_jᵀ e_a) v_{j,a}`            | `visibility`                     | [40](Oet/OperatorEquivalence.lean#L40) |
| `λ₁₄ = ln 2 / 5700 yr⁻¹`                           | `lam14 : ℝ` (explicit argument)  | n/a  |

## Lemmas, theorem, and proof steps

| Paper                                                          | Lean declaration         | Line |
|----------------------------------------------------------------|--------------------------|------|
| `w_jᵀ e_a` is the atmospheric component of `w_j`               | `left_dot_ea`            | [43](Oet/OperatorEquivalence.lean#L43) |
| Completeness of the eigenbasis, `V Wᵀ = 1`                     | `complete`               | [47](Oet/OperatorEquivalence.lean#L47) |
| Eigenbasis expansion of any vector                             | `reconstruct`            | [51](Oet/OperatorEquivalence.lean#L51) |
| Proof: `e_a = Σ_j (w_jᵀ e_a) v_j`                              | `atm_eigen_expansion`    | [55](Oet/OperatorEquivalence.lean#L55) |
| `−λ₁₄ I` shift, right eigenvectors unchanged                   | `eigen_shift_right`      | [66](Oet/OperatorEquivalence.lean#L66) |
| `−λ₁₄ I` shift, left eigenvectors unchanged                    | `eigen_shift_left`       | [74](Oet/OperatorEquivalence.lean#L74) |
| Modal coordinates evolve as `e^{μ_j t}`                        | `modal_evolution`        | [85](Oet/OperatorEquivalence.lean#L85) |
| Modal solution of a linear system sharing the eigenvectors     | `modal_solution`         | [126](Oet/OperatorEquivalence.lean#L126) |
| Proof: solution of (68) with `δX(0) = α e_a`                   | `bomb14c_solution`       | [143](Oet/OperatorEquivalence.lean#L143) |
| Proof: Duhamel solution of (67) for `δe(t) = β e_a δ(t)`       | `mass_impulse_solution`  | [157](Oet/OperatorEquivalence.lean#L157) |
| Eq. (69)                                                       | `bomb14c_atm`            | [168](Oet/OperatorEquivalence.lean#L168) |
| Eq. (70)                                                       | `mass_atm`               | [180](Oet/OperatorEquivalence.lean#L180) |
| Theorem (Operator-equivalence bound)                           | `operator_equivalence`   | [194](Oet/OperatorEquivalence.lean#L194) |
| Hypothesis (iv) applied to `δR_a`                              | `observed_ratio_modes`   | [211](Oet/OperatorEquivalence.lean#L211) |

**Reading notes.**

- `V` and `W` are square `ι × ι` matrices: one right and one left
  eigenvector per reservoir, as in the theorem's hypothesis on the
  eigenstructure of `A`. `Wᵀ V = 1` is exactly `w_jᵀ v_k = δ_jk`.
- `complete` derives `V Wᵀ = 1` from `Wᵀ V = 1` (a left inverse of a square
  matrix is a right inverse). This is what licenses the proof's first step,
  "Decompose the atmospheric unit vector in the right eigenbasis."
- `modal_evolution` carries the proof's solution step. For each mode `j`,
  the coordinate `y_j(t) = w_jᵀ x(t)` satisfies `y_j' = μ_j y_j`, so
  `y_j(t) e^{−μ_j t}` has zero derivative and is constant. Reconstruction
  with `V Wᵀ = 1` gives the full vector solution.
- The theorem's conclusion lists the same declaration `visibility a j` in
  both (69) and (70). That is the statement "the atmospheric visibility
  product `(w_jᵀ e_a) v_{j,a}` is the same in both."

## Scope statement

Hypotheses (i)–(iv) of the theorem enter Lean as follows.

- **(i) Linearity.** Encoded by the linear form of the dynamics: the
  hypotheses `hode` state `δX' = (A − λ₁₄ I) δX` and `δM' = A δM`. The paper
  justifies linearity empirically (single-exponential decay over 54 yr;
  constancy of `κ_in` to ±0.4% across a 31.6% rise in `M_a`, §9).
- **(ii) Shared eigenvectors.** `δM` and `δX` evolve under (67) and (68).
  That `A − λ₁₄ I` has the same left and right eigenvectors as `A`, with
  every eigenvalue shifted by `−λ₁₄`, is proved in Lean
  (`eigen_shift_left`, `eigen_shift_right`).
- **(iii) Bomb-¹⁴C impulse.** `δX(0) = α e_a`, with no subsequent source.
- **(iv) Ratio proportional to content.** `δR_a(t) = κ δX_a(t)`, used in
  `observed_ratio_modes`. The paper justifies this from `M_a` not being
  materially perturbed by the bomb pulse.

The emission impulse `δe(t) = β e_a δ(t)` is a Dirac delta, which is not a
function. Lean encodes it by its Duhamel solution: `δM(0⁺) = β e_a` and
`δM' = A δM` for `t ≥ 0`. Both solutions are required only for `t ≥ 0`:
continuity on `[0, ∞)` and the right derivative at each `t ≥ 0`.

**What Lean certifies:** from the eigenstructure of `A` and hypotheses
(i)–(iv), the full solutions of (67) and (68), eqs. (69) and (70), and the
identity of the visibility product in both.

**What the paper justifies outside Lean:** that the physical carbon system
satisfies hypotheses (i) and (iv).

## Axioms

Running `#print axioms` on the main theorems produces:

```
'OET.EigenData.operator_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound]
'OET.EigenData.observed_ratio_modes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the three standard Lean kernel axioms: propositional
extensionality, classical choice, and well-definedness of quotient types.
Nothing beyond classical mathematics.

## Reproducing the verification

```
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source $HOME/.elan/env
git clone https://github.com/cohler/oet-lean.git
cd oet-lean
lake exe cache get
lake build
```

Expected final line: `Build completed successfully`. Every proof in
`Oet/OperatorEquivalence.lean` has been accepted by the Lean 4 kernel.

## Continuous verification

Every push to `main` re-runs `lake build` on a fresh GitHub Actions
Ubuntu runner with no cached state from this repository's authors. Status:

![Lean build](https://github.com/cohler/oet-lean/actions/workflows/lean_action_ci.yml/badge.svg)
