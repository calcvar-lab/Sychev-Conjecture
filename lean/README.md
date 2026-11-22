# Tonelli's partial regularity for 1D variational obstacle problems — a Lean 4 formalization

This repository contains a complete formalization in [Lean 4](https://lean-lang.org/) and
[Mathlib](https://github.com/leanprover-community/mathlib4) of the main results of the paper

> O. Anza Hafsa, A. Hachache and J.-P. Mandallena, *Sychev's conjecture and Tonelli's partial
> regularity for one-dimensional obstacle problems*.

The [interactive Visual Paper](../website/index.html) and its [sources](../website/source/) are included in the repository. See the [project README](../README.md#visual-paper) to run it locally.

Theorem, lemma, section and equation numbers below refer to the current version of the paper.

**Status: complete.** The main theorem and both corollaries are proved, with no `sorry`.
They depend only on the standard axioms of classical mathematics:

```
'TonelliObstacle.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TonelliObstacle.sychev_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
'TonelliObstacle.C1_near_contact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## The mathematical result

Let `L(x, w, v)` be a Lagrangian on `[a,b] × ℝ × ℝ` and let `f < g` be continuous obstacles. We consider
minimizers of `∫ₐᵇ L(x, u, u′) dx` among absolutely continuous `u` with `u(a) = A`,
`u(b) = B` and `f ≤ u ≤ g`. Assume:

* **(H₁)** `L` is locally Hölder continuous in `(x, w)`, locally uniformly in `v`;
* **(H₂)** `L_vv` exists, is continuous, and `L_vv ≥ μ > 0`;
* **(O_f)** `D₋f(x) ≤ D⁺f(x)` at contact points with `f` (no "concave corner");
* **(O_g)** `D₊g(x) ≤ D⁻g(x)` at contact points with `g` (no "convex corner").

**Theorem 2.2.** Every finite-energy solution `u` has *Tonelli's partial regularity*: `u′`
exists everywhere in `[-∞, ∞]`, is continuous, and is infinite only on a null set. Moreover,
(i) at contact points `u′` is given by the Dini derivates of the obstacle, and (ii) `u` is
strictly differentiable at every point.

**Corollary 2.3 (Sychev's conjecture for finite-energy solutions).** If `f` and `g` have a
derivative in `[-∞, ∞]` at every interior point (e.g. `f, g ∈ W^{1,1}_T`), every finite-energy
solution has Tonelli's partial regularity, with `u′ = f′` on `{u = f}` and `u′ = g′` on `{u = g}`.
If `inf J < ∞`, this applies to *all* solutions.

**Corollary 2.4.** If `f` and `g` are differentiable, with no Dini-type condition on their moduli of continuity, the
singular set `{u′ = ±∞}` is closed and contained in `{a, b} ∪ {f < u < g}`. In particular, `u`
is `C¹` near every interior contact point.

## Where to find what

The Lean files follow the structure of the paper, with a shift in numbering: `Section2.lean`
corresponds to Section 3 of the paper (preliminaries), `Section3.lean` to Section 4 (local
structure near the obstacles) and `Section4.lean` to Section 5 (proof of the main result).
The comments inside the Lean files still use the numbering of an earlier draft.

### Main results

| Paper | Lean | File |
|---|---|---|
| Definitions (W^{1,1}, Dini derivates, Tonelli regularity, 𝒜_{f,g}, (H₁), (H₂), …) | `IsW11`, `dUpperRight`, …, `IsTonelliDeriv`, `TonelliRegular`, `Admissible`, `IsFiniteEnergySolution`, `HypH1`, `HypH2` | `Project/Statement.lean` |
| Theorem 2.2 | `main_theorem` | `Project/Main.lean` |
| Corollary 2.3 | `sychev_conjecture`, `sychev_conjecture_deriv`, `sychev_conjecture_of_tonelli`, `sychev_conjecture_all_solutions` | `Project/Main.lean` |
| Corollary 2.4 | `C1_near_contact`, `C1_singular_set`, `C1_corollary` | `Project/Main.lean` |
| Solutions without finite-energy assumption (Remark 2.6(c), Corollary 2.3(ii)) | `energyE`, `IsSolution`, `isFiniteEnergySolution_iff`, `finiteEnergy_of_inf_lt_top` | `Project/Main.lean` |

### Remarks of the paper — `Project/Remarks.lean`

| Paper | Lean |
|---|---|
| Remark 2.1(a): `L_v` is continuous | `Lv_continuousOn`, `hypH2_Lv_continuousOn` |
| Remark 2.1(b): the energy is well defined in `]-∞, ∞]` | `energyE_eq_lintegral` |
| Remark 2.1(c): Hölder continuity in all variables implies (H₁) | `HypHolderAll`, `hypH1_of_holderAll` |
| Remark 2.5: for `C¹` obstacles, every solution has finite energy | `isFiniteEnergySolution_of_C1`, `C1_corollary_all_solutions` |
| Remark 2.6(a): convex and semiconvex obstacles | `dini_lower_of_semiconvex`, `dini_upper_of_semiconcave`, `Of_of_semiconvex`, `Og_of_semiconcave` |
| Remark 2.6(b): (O_f) and (O_g) cannot be dropped | `remark_2_6b_lower`, `remark_2_6b_upper` |
| Remark 2.6(c): the finite energy assumption cannot be dropped | `remark_2_6c` |

### Section 3 of the paper (preliminaries) — `Project/Section2.lean`

| Paper | Lean |
|---|---|
| Lemma 3.1 (a priori bounds), inequalities (3.1)–(3.3) | `lower_bound_L`, `holder_half` |
| Definition 3.2 and Remark 3.3 (good intervals), inequality (3.4) | `good_interval_ineq` |
| Lemma 3.4 (basic estimate on good intervals) | `basic_estimate` (with `Lv_holder`, `pointwise_F`, `integral_step`) |
| Θ and E (3.8), Lemma 3.6 (properties of Θ and E) | `ThetaSet`, `Theta`, `Theta.nonneg`, `Theta.mono`, `Theta.holder`, `cs_of_good`; `E` and `LowerFrame.E_tendsto_zero` in `Section3.lean` |
| Choice of ρ₀, Definition 3.7 (types), Lemma 3.9 (dichotomy) | `exists_rho0`, `lowerType_of_gap`, `upperType_of_gap`; `LowerType`, `UpperType` in `Section4.lean` |
| Lemma 3.10 (free chords) | built into `lowerFrame_of` and `upperFrame_of` |
| Definition 3.11 and Lemma 3.12 (symmetries (R_v), (R_h)) | `upperFrame_of`, `slope_reflect`, `LowerFrame.reflect` (`Section3.lean`), `slope_neg_fun`, `slope_reflect_gen` (`Section4.lean`) |
| Assembling Section 3 | `lowerFrame_of`, `upperFrame_of`, `global_frame` |

### Section 4 of the paper (local structure near the obstacles) — `Project/Section3.lean`

| Paper | Lean |
|---|---|
| Lemma 4.1 (approximate concavity), inequality (4.1) | `LowerFrame.approx_concave`, `approx_concave_right`, `approx_concave_left`, `approx_concave_center` |
| Lemma 4.2 (one-sided monotonicity of slopes) | `LowerFrame.slope_mono_right`, `LowerFrame.slope_mono_left` |
| Lemma 4.3 (one-sided derivatives, no convex corner) | `LowerFrame.exists_right_deriv`, `LowerFrame.exists_left_deriv`, `LowerFrame.no_convex_corner` |

### Section 5 of the paper (proof of the main result) — `Project/Section4.lean`

| Paper | Lean |
|---|---|
| Lemma 5.1 (existence of the derivative) | `GlobalFrame.exists_right`, `GlobalFrame.exists_left`, `GlobalFrame.one_sided_eq` |
| Lemma 5.2 (strict differentiability) | `LowerFrame.strict_real`, `LowerFrame.strict_top`, `LowerFrame.strict_ereal`, `GlobalFrame.strict_deriv`, `GlobalFrame.strict_tendsto` |
| Proof of Theorem 2.2 | `GlobalFrame.main`, then `main_theorem` in `Main.lean` |

### Structure of the proof

The proof is organized around two abstract interfaces:

* `LowerFrame u c d Θ` (`Section3.lean`, Section 4 of the paper) records what the concavity
  argument needs on an interval `[c, d]` of lower type: continuity of `u`, a function `Θ(K, ε)`
  that is nonnegative, monotone and Hölder-small, and the Cauchy–Schwarz inequality (3.10) for
  chords lying above `u`. These are exactly the properties of Lemma 3.6 of the paper.
* `GlobalFrame u f g a b Θ ρ₀` (`Section4.lean`, Section 5 of the paper) records the covering of
  `[a, b]` by short intervals of lower type (a `LowerFrame` for `u`) and of upper type (a
  `LowerFrame` for `-u`, by the symmetry (R_v)), together with the behavior at contact points and
  at free points.

`Section2.lean` (Section 3 of the paper) proves that a finite-energy solution satisfies these
interfaces (`global_frame`).
`Main.lean` combines this with `GlobalFrame.main` and adds the measure-zero statement for
`{u′ = ±∞}`, using Lebesgue differentiation.

### Formalization choices

* Functions are defined on all of `ℝ`, but only their values on `[a, b]` matter.
* Slopes and derivatives with values in `[-∞, ∞]` live in `EReal`. The slope `k_u(s,t)` is
  Mathlib's `slope u s t`.
* `u ∈ W^{1,1}([a,b])` means that `u` is a constant plus the primitive of an integrable function,
  which is equivalent to absolute continuity.
* In (H₁), arbitrary compact sets are replaced by the boxes `[a,b] × [-R,R] × [-R,R]`, which is
  equivalent.
* "Finite-energy solution" means: `u` is admissible, `L(·, u, u′)` is integrable, and
  `J(u) ≤ J(v)` for every admissible `v` of finite energy. `isFiniteEnergySolution_iff`
  proves that this is equivalent to "`u ∈ 𝒮_{f,g}` and `J(u) < ∞`", for the `]-∞, +∞]`-valued energy.

## Building

The project uses Lean `v4.33.1` and the matching Mathlib.

```bash
cd lean
lake exe cache get   # download precompiled Mathlib
lake build
```

To check the axioms, create a file `Check.lean` containing:

```lean
import Project.Main
import Project.Remarks
#print axioms TonelliObstacle.main_theorem
#print axioms TonelliObstacle.sychev_conjecture
#print axioms TonelliObstacle.C1_near_contact
#print axioms TonelliObstacle.remark_2_6b_lower
#print axioms TonelliObstacle.remark_2_6c
```

and run `lake env lean Check.lean`.

## License

See [`LICENSE`](../LICENSE).
