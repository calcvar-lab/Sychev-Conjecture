import Mathlib

/-!
# Tonelli's partial regularity for 1D variational obstacle problems

Squelette de formalisation : définitions et énoncés principaux de l'article.
Les théorèmes principaux sont énoncés et démontrés dans `Project/Main.lean`.

Conventions :
* les fonctions sont définies sur `ℝ` tout entier, mais seules leurs valeurs sur
  `[a,b] = Icc a b` interviennent ;
* les pentes et dérivées à valeurs dans `[-∞,∞]` sont prises dans `EReal` ;
* la pente `k_u(s,t)` est la fonction `slope u s t` de Mathlib.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace TonelliObstacle

/-! ## Notations de l'introduction -/

/-- `u ∈ W^{1,1}([a,b])` : `u` est la primitive d'une fonction intégrable sur `[a,b]`
(équivalent à l'absolue continuité). -/
def IsW11 (a b : ℝ) (u : ℝ → ℝ) : Prop :=
  ∃ g : ℝ → ℝ, IntervalIntegrable g volume a b ∧
    ∀ x ∈ Icc a b, u x = u a + ∫ t in a..x, g t

/-- La pente `k_h(s,t)`, vue dans `[-∞,∞]`. -/
def eslope (h : ℝ → ℝ) (s t : ℝ) : EReal :=
  ((slope h s t : ℝ) : EReal)

/-- Dérivé de Dini `D⁺h(x)`. -/
def dUpperRight (h : ℝ → ℝ) (x : ℝ) : EReal :=
  limsup (fun t => eslope h x (x + t)) (𝓝[>] (0 : ℝ))

/-- Dérivé de Dini `D₊h(x)`. -/
def dLowerRight (h : ℝ → ℝ) (x : ℝ) : EReal :=
  liminf (fun t => eslope h x (x + t)) (𝓝[>] (0 : ℝ))

/-- Dérivé de Dini `D⁻h(x)`. -/
def dUpperLeft (h : ℝ → ℝ) (x : ℝ) : EReal :=
  limsup (fun t => eslope h (x - t) x) (𝓝[>] (0 : ℝ))

/-- Dérivé de Dini `D₋h(x)`. -/
def dLowerLeft (h : ℝ → ℝ) (x : ℝ) : EReal :=
  liminf (fun t => eslope h (x - t) x) (𝓝[>] (0 : ℝ))

/-- `p ∈ [-∞,∞]` est la dérivée de `u` en `x` relativement à `[a,b]`
(dérivée unilatérale aux extrémités `a` et `b`). -/
def HasEDerivWithinIcc (a b : ℝ) (u : ℝ → ℝ) (p : EReal) (x : ℝ) : Prop :=
  Tendsto (fun t => eslope u x t) (𝓝[Icc a b \ {x}] x) (𝓝 p)

/-- `u'` est une dérivée « au sens de Tonelli » de `u` sur `[a,b]` :
elle existe partout dans `[-∞,∞]`, elle est continue, et l'ensemble où elle est
infinie est de mesure nulle. (L'ouverture de `Ω_u` dans `[a,b]` découle de la continuité.) -/
def IsTonelliDeriv (a b : ℝ) (u : ℝ → ℝ) (u' : ℝ → EReal) : Prop :=
  (∀ x ∈ Icc a b, HasEDerivWithinIcc a b u (u' x) x) ∧
  ContinuousOn u' (Icc a b) ∧
  volume {x ∈ Icc a b | u' x = ⊤ ∨ u' x = ⊥} = 0

/-- `u ∈ W^{1,1}_T([a,b])` : régularité partielle de Tonelli. -/
def TonelliRegular (a b : ℝ) (u : ℝ → ℝ) : Prop :=
  IsW11 a b u ∧ ∃ u' : ℝ → EReal, IsTonelliDeriv a b u u'

/-! ## Section 2 : cadre -/

/-- L'ensemble admissible `𝒜_{f,g}`. -/
def Admissible (a b A B : ℝ) (f g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {u | IsW11 a b u ∧ u a = A ∧ u b = B ∧ ∀ x ∈ Icc a b, f x ≤ u x ∧ u x ≤ g x}

/-- La densité d'énergie `x ↦ L(x, u(x), u'(x))`. -/
def energyDensity (L : ℝ → ℝ → ℝ → ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun x => L x (u x) (deriv u x)

/-- `𝒥_L(u;[a,b]) < ∞`. Comme `L(·,u,u')` est minorée sur `𝒜_{f,g}` (Remarque 2.1(b)),
l'énergie finie équivaut à l'intégrabilité de la densité. -/
def FiniteEnergy (a b : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (u : ℝ → ℝ) : Prop :=
  IntegrableOn (energyDensity L u) (Icc a b)

/-- La valeur de `𝒥_L(u;[a,b])`, qui n'a de sens que si l'énergie est finie
(en Lean, l'intégrale d'une fonction non intégrable vaut `0`). -/
def energy (a b : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (u : ℝ → ℝ) : ℝ :=
  ∫ x in a..b, energyDensity L u x

/-- `u ∈ 𝒮_{f,g}` et `𝒥_L(u;[a,b]) < ∞`. Les compétiteurs d'énergie infinie
ne posent aucune contrainte, car `𝒥_L(u) ≤ +∞` trivialement. -/
def IsFiniteEnergySolution (a b A B : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (f g u : ℝ → ℝ) : Prop :=
  u ∈ Admissible a b A B f g ∧ FiniteEnergy a b L u ∧
    ∀ v ∈ Admissible a b A B f g, FiniteEnergy a b L v →
      energy a b L u ≤ energy a b L v

/-- Hypothèse (H₁) : `L` est localement höldérienne en `(x,w)`, localement uniformément
en `v`. Les compacts de `[a,b] × ℝ × ℝ` sont remplacés par les pavés
`[a,b] × [-R,R] × [-R,R]`, ce qui est équivalent. -/
def HypH1 (a b : ℝ) (L : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ R : ℝ, ∃ C : ℝ, 0 < C ∧ ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
    ∀ x₁ ∈ Icc a b, ∀ x₂ ∈ Icc a b, ∀ w₁ w₂ v : ℝ,
      |w₁| ≤ R → |w₂| ≤ R → |v| ≤ R →
        |L x₁ w₁ v - L x₂ w₂ v| ≤ C * (|x₁ - x₂| + |w₁ - w₂|) ^ α

/-- Hypothèse (H₂) : `L_vv` existe, est continue et `L_vv ≥ μ > 0`. -/
def HypH2 (a b : ℝ) (L : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∃ Lv Lvv : ℝ → ℝ → ℝ → ℝ, ∃ μ : ℝ, 0 < μ ∧
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Lvv p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))) ∧
    ∀ x ∈ Icc a b, ∀ w v : ℝ,
      HasDerivAt (fun v => L x w v) (Lv x w v) v ∧
      HasDerivAt (fun v => Lv x w v) (Lvv x w v) v ∧
      μ ≤ Lvv x w v

/-! ## Théorème 2.2 et corollaires

Les énoncés et leurs preuves se trouvent dans `Project/Main.lean`
(`main_theorem`, `sychev_conjecture`, `C1_near_contact`). -/

/-! ## Section 2.4 : intervalles de type inférieur et cordes libres -/

/-- La fonction `u_{s,t}` : la corde de `u` sur `[s,t]`, et `u` ailleurs. -/
def chord (u : ℝ → ℝ) (s t : ℝ) : ℝ → ℝ :=
  fun x => if x ∈ Icc s t then u s + slope u s t * (x - s) else u x

/-- **Lemme 2.9** (cordes libres), cas d'un intervalle `J = [c,d]` de type inférieur
(`max_J u < min_J g`) : une corde située au-dessus de `u` est admissible. -/
lemma free_chord_lower (u f g : ℝ → ℝ) (c d σ τ : ℝ)
    (hστ : σ < τ) (hJ : Icc σ τ ⊆ Icc c d)
    (hlow : ∀ y ∈ Icc c d, ∀ z ∈ Icc c d, u y < g z)
    (hfu : ∀ x ∈ Icc σ τ, f x ≤ u x)
    (habove : ∀ x ∈ Icc σ τ, u x ≤ chord u σ τ x) :
    ∀ x ∈ Icc σ τ, f x ≤ chord u σ τ x ∧ chord u σ τ x ≤ g x := by
  intro x hx
  -- les points σ, τ et x sont dans J = [c,d]
  have hσJ : σ ∈ Icc c d := hJ ⟨le_rfl, hστ.le⟩
  have hτJ : τ ∈ Icc c d := hJ ⟨hστ.le, le_rfl⟩
  have hxJ : x ∈ Icc c d := hJ hx
  -- valeur de la corde en x
  have hc : chord u σ τ x = u σ + slope u σ τ * (x - σ) := by
    simp only [chord, if_pos hx]
  -- (τ - σ) k(σ,τ) = u(τ) - u(σ)
  have hk : (τ - σ) * slope u σ τ = u τ - u σ := by
    simpa using sub_smul_slope u σ τ
  constructor
  · -- minoration : f ≤ u ≤ corde
    exact (hfu x hx).trans (habove x hx)
  · -- majoration : corde ≤ max(u(σ), u(τ)) < g(x)
    have hgσ : u σ < g x := hlow σ hσJ x hxJ
    have hgτ : u τ < g x := hlow τ hτJ x hxJ
    rw [hc]
    rcases le_total 0 (slope u σ τ) with h | h
    · -- pente positive : corde ≤ u(τ)
      nlinarith [mul_le_mul_of_nonneg_left hx.2 h]
    · -- pente négative : corde ≤ u(σ)
      nlinarith [mul_nonneg (neg_nonneg.mpr h) (sub_nonneg.mpr hx.1)]

/-- **Lemme 2.9** (cordes libres), cas d'un intervalle `J = [c,d]` de type supérieur
(`min_J u > max_J f`) : une corde située au-dessous de `u` est admissible. -/
lemma free_chord_upper (u f g : ℝ → ℝ) (c d σ τ : ℝ)
    (hστ : σ < τ) (hJ : Icc σ τ ⊆ Icc c d)
    (hup : ∀ y ∈ Icc c d, ∀ z ∈ Icc c d, f z < u y)
    (hug : ∀ x ∈ Icc σ τ, u x ≤ g x)
    (hbelow : ∀ x ∈ Icc σ τ, chord u σ τ x ≤ u x) :
    ∀ x ∈ Icc σ τ, f x ≤ chord u σ τ x ∧ chord u σ τ x ≤ g x := by
  intro x hx
  -- les points σ, τ et x sont dans J = [c,d]
  have hσJ : σ ∈ Icc c d := hJ ⟨le_rfl, hστ.le⟩
  have hτJ : τ ∈ Icc c d := hJ ⟨hστ.le, le_rfl⟩
  have hxJ : x ∈ Icc c d := hJ hx
  -- valeur de la corde en x
  have hc : chord u σ τ x = u σ + slope u σ τ * (x - σ) := by
    simp only [chord, if_pos hx]
  -- (τ - σ) k(σ,τ) = u(τ) - u(σ)
  have hk : (τ - σ) * slope u σ τ = u τ - u σ := by
    simpa using sub_smul_slope u σ τ
  constructor
  · -- minoration : f(x) < min(u(σ), u(τ)) ≤ corde
    have hfσ : f x < u σ := hup σ hσJ x hxJ
    have hfτ : f x < u τ := hup τ hτJ x hxJ
    rw [hc]
    rcases le_total 0 (slope u σ τ) with h | h
    · -- pente positive : corde ≥ u(σ)
      nlinarith [mul_nonneg h (sub_nonneg.mpr hx.1)]
    · -- pente négative : corde ≥ u(τ)
      nlinarith [mul_le_mul_of_nonpos_left hx.2 h]
  · -- majoration : corde ≤ u ≤ g
    exact (hbelow x hx).trans (hug x hx)

end TonelliObstacle
