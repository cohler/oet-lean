# oet-lean

Lean 4 formalization of the Operator-Equivalence Theorem.

**Paper:** Cohler, J. and Soon, W. *Bomb-Radiocarbon Decay Falsifies the IPCC (Part II).*
Science of Climate Change. Theorem and proof: Appendix A.2.
The version matching this repository state is
[`paper/bomb14c-scc-part2.pdf`](paper/bomb14c-scc-part2.pdf).

![Lean build](https://github.com/cohler/oet-lean/actions/workflows/lean_action_ci.yml/badge.svg)

## What is verified

The file [`Oet/OperatorEquivalence.lean`](Oet/OperatorEquivalence.lean)
contains the Lean 4 formalization of the theorem and its proof. The Lean
kernel accepts every proof. Verified items:

| Paper (Appendix A.2)                                        | Lean name                 |
|-------------------------------------------------------------|---------------------------|
| `−λ₁₄ I` shifts every eigenvalue, eigenvectors unchanged (right) | `eigen_shift_right`  |
| `−λ₁₄ I` shifts every eigenvalue, eigenvectors unchanged (left)  | `eigen_shift_left`   |
| Proof: `e_a = Σ_j (w_jᵀ e_a) v_j`                            | `atm_eigen_expansion`     |
| Proof: solution of (68), `δX(t) = α Σ_j (w_jᵀ e_a) e^{(λ_j − λ₁₄)t} v_j` | `bomb14c_solution` |
| Proof: Duhamel solution of (67), `δM(t) = β Σ_j (w_jᵀ e_a) e^{λ_j t} v_j` | `mass_impulse_solution` |
| Eq. (69)                                                    | `bomb14c_atm`             |
| Eq. (70)                                                    | `mass_atm`                |
| Theorem (Operator-equivalence bound)                        | `operator_equivalence`    |
| Hypothesis (iv) applied to the observed ratio anomaly       | `observed_ratio_modes`    |

Full paper-to-Lean mapping with line numbers and notation notes:
[`CORRESPONDENCE.md`](CORRESPONDENCE.md).

## Axioms

The main theorems reduce to the three standard Lean kernel axioms
and nothing else:

```
'OET.EigenData.operator_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound]
'OET.EigenData.observed_ratio_modes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`propext` is propositional extensionality. `Classical.choice` is classical
choice. `Quot.sound` is the soundness of quotient types. These are the
standard foundations of classical mathematics in Lean 4.

## What Lean certifies, and what the paper justifies outside Lean

The theorem's hypotheses enter Lean as explicit premises:

- (i) Linearity: the dynamics are the linear systems (67) and (68).
- (ii) `δM` and `δX` evolve under (67) and (68). That the two operators share
  the eigenvectors of `A` is proved in Lean (`eigen_shift_right`,
  `eigen_shift_left`), not assumed.
- (iii) `δX(0) = α e_a`.
- (iv) `δR_a(t) = κ δX_a(t)`.

The mass impulse `δe(t) = β e_a δ(t)` is encoded by its Duhamel solution:
`δM(0⁺) = β e_a` and `δM' = A δM` for `t ≥ 0`.

The paper justifies hypotheses (i) and (iv) empirically (§9 and the
statement of the theorem). Lean certifies that (69), (70), and the shared
visibility product follow from the hypotheses.

See [`CORRESPONDENCE.md`](CORRESPONDENCE.md) for the full scope statement.

## Reproducing the verification

Install the Lean toolchain manager, clone this repository, pull the
Mathlib build cache, and run `lake build`:

```
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source $HOME/.elan/env
git clone https://github.com/cohler/oet-lean.git
cd oet-lean
lake exe cache get
lake build
```

Expected final line: `Build completed successfully`.

Every push to `main` also re-runs this build on a fresh GitHub Actions
Ubuntu runner with no cached state from the authors. The badge at the top
reports the current status.

## Versioning

Each tag freezes the Lean source, this documentation, and the matching
paper PDF (`paper/bomb14c-scc-part2.pdf`) together. Tags are never
moved; a new paper version gets a new tag.

| Tag    | Paper version | Date          |
|--------|---------------|---------------|
| `v1.0` | Manuscript    | November 2026 |

To build the version matching a given paper, run `git checkout <tag>`
before `lake build`.

## Toolchain

- Lean 4 (version pinned in [`lean-toolchain`](lean-toolchain))
- Mathlib (revision pinned in [`lake-manifest.json`](lake-manifest.json))
