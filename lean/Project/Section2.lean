import Project.Section4

/-!
# Section 2 : préliminaires

## § 2.4 : le choix de `ρ₀` et les intervalles de type inférieur et supérieur

On montre que, si `u`, `f`, `g` sont continues sur `[a,b]` avec `f < g` et `f ≤ u ≤ g`,
il existe `ρ₀ > 0` (aussi petit qu'on veut) tel que :
* tout intervalle de longueur `≤ ρ₀` est de type inférieur ou supérieur ;
* un intervalle court contenant un point de contact avec `f` (resp. `g`) est de type
  inférieur (resp. supérieur) ;
* un point libre admet un voisinage court qui est des deux types.
-/

open Set Filter Topology

noncomputable section

namespace TonelliObstacle

/-- Si `g - u ≥ 2ε` en un point `x₀` de `J` et si `u` et `g` varient de moins de `ε` sur `J`,
alors `J` est de type inférieur. -/
lemma lowerType_of_gap {u g : ℝ → ℝ} {c d x₀ ε : ℝ} (hgap : 2 * ε ≤ g x₀ - u x₀)
    (hu : ∀ y ∈ Icc c d, |u y - u x₀| < ε) (hg : ∀ z ∈ Icc c d, |g z - g x₀| < ε) :
    LowerType u g c d := by
  intro y hy z hz
  have h1 := (abs_lt.mp (hu y hy)).2
  have h2 := (abs_lt.mp (hg z hz)).1
  linarith

/-- Si `u - f ≥ 2ε` en un point `x₀` de `J` et si `u` et `f` varient de moins de `ε` sur `J`,
alors `J` est de type supérieur. -/
lemma upperType_of_gap {u f : ℝ → ℝ} {c d x₀ ε : ℝ} (hgap : 2 * ε ≤ u x₀ - f x₀)
    (hu : ∀ y ∈ Icc c d, |u y - u x₀| < ε) (hf : ∀ z ∈ Icc c d, |f z - f x₀| < ε) :
    UpperType u f c d := by
  intro y hy z hz
  have h1 := (abs_lt.mp (hu y hy)).1
  have h2 := (abs_lt.mp (hf z hz)).2
  linarith

/-- Continuité uniforme sur `[a,b]`, sous forme `ε`-`δ`. -/
lemma uniform_on_Icc {φ : ℝ → ℝ} {a b : ℝ} (hφ : ContinuousOn φ (Icc a b)) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |x - y| < δ → |φ x - φ y| < ε := by
  obtain ⟨δ, hδ, H⟩ :=
    Metric.uniformContinuousOn_iff.mp (isCompact_Icc.uniformContinuousOn_of_continuous hφ) ε hε
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  have := H x hx y hy (by rwa [Real.dist_eq])
  rwa [Real.dist_eq] at this

/-- **Le choix de `ρ₀`** (§ 2.4) et les propriétés des intervalles de type inférieur
et supérieur. -/
theorem exists_rho0 {u f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (hfg : ∀ x ∈ Icc a b, f x < g x)
    {ρ₁ : ℝ} (hρ₁ : 0 < ρ₁) :
    ∃ ρ₀ > 0, ρ₀ ≤ ρ₁ ∧
      (∀ c d, a ≤ c → c < d → d ≤ b → d - c ≤ ρ₀ →
        LowerType u g c d ∨ UpperType u f c d) ∧
      (∀ c d x, a ≤ c → c < d → d ≤ b → d - c ≤ ρ₀ → x ∈ Icc c d → u x = f x →
        LowerType u g c d) ∧
      (∀ c d x, a ≤ c → c < d → d ≤ b → d - c ≤ ρ₀ → x ∈ Icc c d → u x = g x →
        UpperType u f c d) ∧
      (∀ x ∈ Ioo a b, f x < u x → u x < g x → ∃ c d, a ≤ c ∧ c < x ∧ x < d ∧ d ≤ b ∧
        d - c ≤ ρ₀ ∧ LowerType u g c d ∧ UpperType u f c d) := by
  -- η₀ = ½ min (g - f) > 0
  obtain ⟨xm, hxm, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) (hg.sub hf)
  obtain ⟨η, hη⟩ : ∃ η, η = (g xm - f xm) / 2 := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; linarith [hfg xm hxm]
  have hgap : ∀ x ∈ Icc a b, 2 * η ≤ g x - f x := fun x hx => by
    have h' : g xm - f xm ≤ g x - f x := isMinOn_iff.mp hmin x hx
    rw [hη]
    linarith
  -- ρ₀ par continuité uniforme de u, f, g (écarts < η/4)
  obtain ⟨δu, hδu, Hu⟩ := uniform_on_Icc hu (show 0 < η / 4 by linarith)
  obtain ⟨δf, hδf, Hf⟩ := uniform_on_Icc hf (show 0 < η / 4 by linarith)
  obtain ⟨δg, hδg, Hg⟩ := uniform_on_Icc hg (show 0 < η / 4 by linarith)
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀, ρ₀ = min (min (min δu δf) δg / 2) ρ₁ := ⟨_, rfl⟩
  have hm1 := min_le_left (min δu δf) δg
  have hm2 := min_le_right (min δu δf) δg
  have hm3 := min_le_left δu δf
  have hm4 := min_le_right δu δf
  have hmpos : 0 < min (min δu δf) δg := lt_min (lt_min hδu hδf) hδg
  have hρpos : 0 < ρ₀ := by rw [hρ₀]; exact lt_min (by linarith) hρ₁
  have hρ1 : ρ₀ ≤ ρ₁ := by rw [hρ₀]; exact min_le_right _ _
  have hρm : ρ₀ ≤ min (min δu δf) δg / 2 := by rw [hρ₀]; exact min_le_left _ _
  -- sur un intervalle court, u, f, g varient de moins de η/4
  have hclose : ∀ c d, a ≤ c → d ≤ b → d - c ≤ ρ₀ → ∀ x₀ ∈ Icc c d,
      (∀ y ∈ Icc c d, |u y - u x₀| < η / 4) ∧ (∀ y ∈ Icc c d, |f y - f x₀| < η / 4) ∧
      (∀ y ∈ Icc c d, |g y - g x₀| < η / 4) := by
    intro c d hac hdb hlen x₀ hx₀
    have hx₀ab : x₀ ∈ Icc a b := ⟨by linarith [hx₀.1], by linarith [hx₀.2]⟩
    have hdist : ∀ y ∈ Icc c d, ∀ δ, ρ₀ < δ → |y - x₀| < δ := fun y hy δ hδ =>
      abs_sub_lt_iff.mpr ⟨by linarith [hy.2, hx₀.1], by linarith [hy.1, hx₀.2]⟩
    refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
    · exact Hu y ⟨by linarith [hy.1], by linarith [hy.2]⟩ x₀ hx₀ab (hdist y hy δu (by linarith))
    · exact Hf y ⟨by linarith [hy.1], by linarith [hy.2]⟩ x₀ hx₀ab (hdist y hy δf (by linarith))
    · exact Hg y ⟨by linarith [hy.1], by linarith [hy.2]⟩ x₀ hx₀ab (hdist y hy δg (by linarith))
  refine ⟨ρ₀, hρpos, hρ1, ?_, ?_, ?_, ?_⟩
  · -- dichotomie, au point x₀ = c
    intro c d hac hcd hdb hlen
    have hc : c ∈ Icc c d := ⟨le_rfl, hcd.le⟩
    obtain ⟨Cu, Cf, Cg⟩ := hclose c d hac hdb hlen c hc
    have hcab : c ∈ Icc a b := ⟨hac, by linarith⟩
    have := hgap c hcab
    by_cases h : η ≤ g c - u c
    · exact Or.inl (lowerType_of_gap (by linarith) Cu Cg)
    · exact Or.inr (upperType_of_gap (by linarith) Cu Cf)
  · -- contact avec f
    intro c d x hac hcd hdb hlen hx h1
    obtain ⟨Cu, Cf, Cg⟩ := hclose c d hac hdb hlen x hx
    have := hgap x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact lowerType_of_gap (by rw [h1]; linarith) Cu Cg
  · -- contact avec g
    intro c d x hac hcd hdb hlen hx h2
    obtain ⟨Cu, Cf, Cg⟩ := hclose c d hac hdb hlen x hx
    have := hgap x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact upperType_of_gap (by rw [h2]; linarith) Cu Cf
  · -- point libre : un voisinage court des deux types
    intro x hx h1 h2
    have hxab : x ∈ Icc a b := ⟨hx.1.le, hx.2.le⟩
    obtain ⟨γ, hγ⟩ : ∃ γ, γ = min (g x - u x) (u x - f x) := ⟨_, rfl⟩
    have hγpos : 0 < γ := by rw [hγ]; exact lt_min (by linarith) (by linarith)
    have hγ1 : γ ≤ g x - u x := by rw [hγ]; exact min_le_left _ _
    have hγ2 : γ ≤ u x - f x := by rw [hγ]; exact min_le_right _ _
    obtain ⟨εu, hεu, Eu⟩ := uniform_on_Icc hu (show 0 < γ / 4 by linarith)
    obtain ⟨εf, hεf, Ef⟩ := uniform_on_Icc hf (show 0 < γ / 4 by linarith)
    obtain ⟨εg, hεg, Eg⟩ := uniform_on_Icc hg (show 0 < γ / 4 by linarith)
    obtain ⟨r, hr⟩ : ∃ r, r = min (min (min εu εf) εg / 2) (min (ρ₀ / 2) (min (x - a) (b - x))) :=
      ⟨_, rfl⟩
    have n1 := min_le_left (min (min εu εf) εg / 2) (min (ρ₀ / 2) (min (x - a) (b - x)))
    have n2 := min_le_right (min (min εu εf) εg / 2) (min (ρ₀ / 2) (min (x - a) (b - x)))
    have n3 := min_le_left (min εu εf) εg
    have n4 := min_le_right (min εu εf) εg
    have n5 := min_le_left εu εf
    have n6 := min_le_right εu εf
    have n7 := min_le_left (ρ₀ / 2) (min (x - a) (b - x))
    have n8 := min_le_right (ρ₀ / 2) (min (x - a) (b - x))
    have n9 := min_le_left (x - a) (b - x)
    have n10 := min_le_right (x - a) (b - x)
    have hεpos : 0 < min (min εu εf) εg := lt_min (lt_min hεu hεf) hεg
    have hrpos : 0 < r := by
      rw [hr]
      exact lt_min (by linarith) (lt_min (by linarith)
        (lt_min (by linarith [hx.1]) (by linarith [hx.2])))
    have hJ : ∀ y ∈ Icc (x - r) (x + r), y ∈ Icc a b ∧ |y - x| < min (min εu εf) εg :=
      fun y hy => ⟨⟨by linarith [hy.1], by linarith [hy.2]⟩,
        abs_sub_lt_iff.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩⟩
    refine ⟨x - r, x + r, by linarith, by linarith, by linarith, by linarith, by linarith,
      lowerType_of_gap (x₀ := x) (ε := γ / 4) (by linarith) (fun y hy => ?_) (fun z hz => ?_),
      upperType_of_gap (x₀ := x) (ε := γ / 4) (by linarith) (fun y hy => ?_) (fun z hz => ?_)⟩
    · exact Eu y (hJ y hy).1 x hxab (lt_of_lt_of_le (hJ y hy).2 (by linarith))
    · exact Eg z (hJ z hz).1 x hxab (lt_of_lt_of_le (hJ z hz).2 (by linarith))
    · exact Eu y (hJ y hy).1 x hxab (lt_of_lt_of_le (hJ y hy).2 (by linarith))
    · exact Ef z (hJ z hz).1 x hxab (lt_of_lt_of_le (hJ z hz).2 (by linarith))

/-! ## § 2.1 : la minoration (2.1) -/

/-- **Formule de Taylor minorée** : si `φ'' ≥ μ`, alors
`φ(v) ≥ φ(v₀) + φ'(v₀)(v - v₀) + (μ/2)(v - v₀)²`. -/
lemma taylor_lower {φ φd φdd : ℝ → ℝ} {μ : ℝ} (h1 : ∀ v, HasDerivAt φ (φd v) v)
    (h2 : ∀ v, HasDerivAt φd (φdd v) v) (hμ : ∀ v, μ ≤ φdd v) (v₀ v : ℝ) :
    φ v₀ + φd v₀ * (v - v₀) + μ / 2 * ((v - v₀) * (v - v₀)) ≤ φ v := by
  -- φ' - μ id est croissante
  have hg1 : ∀ y, HasDerivAt (fun y => φd y - μ * y) (φdd y - μ * 1) y := fun y =>
    (h2 y).sub ((hasDerivAt_id' y).const_mul μ)
  have hmono : Monotone (fun y => φd y - μ * y) :=
    monotone_of_deriv_nonneg (fun y => (hg1 y).differentiableAt)
      (fun y => by rw [(hg1 y).deriv]; linarith [hμ y])
  -- ψ(y) = φ(y) - φ'(v₀) y - (μ/2)(y - v₀)², de dérivée (φ' - μ id)(y) - (φ' - μ id)(v₀)
  have hψ : ∀ y, HasDerivAt (fun y => φ y - φd v₀ * y - μ / 2 * ((y - v₀) * (y - v₀)))
      (φd y - φd v₀ - μ * (y - v₀)) y := fun y =>
    (((h1 y).sub ((hasDerivAt_id' y).const_mul (φd v₀))).sub
      ((((hasDerivAt_id' y).sub_const v₀).mul ((hasDerivAt_id' y).sub_const v₀)).const_mul
        (μ / 2))).congr_deriv (by ring)
  have hcont : ∀ a b, ContinuousOn
      (fun y => φ y - φd v₀ * y - μ / 2 * ((y - v₀) * (y - v₀))) (Icc a b) :=
    fun a b x _ => (hψ x).continuousAt.continuousWithinAt
  -- accroissements finis entre v et v₀
  rcases lt_trichotomy v v₀ with hv | hv | hv
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope _ _ hv (hcont v v₀) (fun x _ => hψ x)
    have hm : φd ξ - μ * ξ ≤ φd v₀ - μ * v₀ := hmono hξ.2.le
    rw [eq_div_iff (sub_ne_zero.mpr hv.ne')] at hξeq
    have := mul_le_mul_of_nonneg_right
      (show φd ξ - φd v₀ - μ * (ξ - v₀) ≤ 0 by linarith) (show (0 : ℝ) ≤ v₀ - v by linarith)
    linarith
  · subst hv
    simp
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope _ _ hv (hcont v₀ v) (fun x _ => hψ x)
    have hm : φd v₀ - μ * v₀ ≤ φd ξ - μ * ξ := hmono hξ.1.le
    rw [eq_div_iff (sub_ne_zero.mpr hv.ne')] at hξeq
    have := mul_le_mul_of_nonneg_right
      (show 0 ≤ φd ξ - φd v₀ - μ * (ξ - v₀) by linarith) (show (0 : ℝ) ≤ v - v₀ by linarith)
    linarith

/-- **La minoration (2.1)** : si `φ'' ≥ μ > 0`, `|φ(0)| ≤ C₀` et `|φ'(0)| ≤ C₀`, alors
`φ(v) ≥ (μ/4) v² - C₀ - C₀²/μ`. -/
lemma lower_bound_L {φ φd φdd : ℝ → ℝ} {μ C₀ : ℝ} (hμpos : 0 < μ)
    (h1 : ∀ v, HasDerivAt φ (φd v) v) (h2 : ∀ v, HasDerivAt φd (φdd v) v)
    (hμ : ∀ v, μ ≤ φdd v) (hC1 : |φ 0| ≤ C₀) (hC2 : |φd 0| ≤ C₀) (v : ℝ) :
    μ / 4 * v ^ 2 - C₀ - C₀ ^ 2 / μ ≤ φ v := by
  have hT := taylor_lower h1 h2 hμ 0 v
  simp only [sub_zero] at hT
  have hL0 := neg_abs_le (φ 0)
  -- L_v(·,·,0) v ≥ -C₀ |v|
  have hLv : -(C₀ * |v|) ≤ φd 0 * v := by
    have h3 := neg_abs_le (φd 0 * v)
    rw [abs_mul] at h3
    have h4 := mul_le_mul_of_nonneg_right hC2 (abs_nonneg v)
    linarith
  -- inégalité de Young : C₀ |v| ≤ (μ/4) v² + C₀²/μ
  have hY : C₀ * |v| ≤ μ / 4 * v ^ 2 + C₀ ^ 2 / μ := by
    have e : μ / 4 * v ^ 2 + C₀ ^ 2 / μ - C₀ * |v| = (μ * |v| - 2 * C₀) ^ 2 / (4 * μ) := by
      rw [← sq_abs v]
      field_simp
      ring
    have : 0 ≤ (μ * |v| - 2 * C₀) ^ 2 / (4 * μ) := by positivity
    linarith
  nlinarith [sq_nonneg v]

/-! ## Outils d'intégration -/

open MeasureTheory

/-- **(A)** Une fonction de `W^{1,1}([a,b])` est dérivable presque partout sur `]a,b[`, de
dérivée la fonction intégrable `g` de sa représentation intégrale (différentiation de
Lebesgue). -/
lemma W11_ae_hasDerivAt {u : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b) (hu : ∀ x ∈ Icc a b, u x = u a + ∫ t in a..x, g t) :
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt u (g x) x := by
  filter_upwards [hg.ae_hasDerivAt_integral] with x hx hxab
  have hxu : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact Ioo_subset_Icc_self hxab
  have hd := (hx hxu a left_mem_uIcc).const_add (u a)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hxab.1 hxab.2] with y hy
  exact hu y (Ioo_subset_Icc_self hy)

/-- **(B)** Inégalité de Cauchy-Schwarz : `(∫ₓʸ g)² ≤ (y - x) ∫ₓʸ g²`. -/
lemma sq_integral_le {g : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hg : IntervalIntegrable g volume x y)
    (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume x y) :
    (∫ t in x..y, g t) ^ 2 ≤ (y - x) * ∫ t in x..y, g t ^ 2 := by
  obtain ⟨S, hS⟩ : ∃ S, S = ∫ t in x..y, g t := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∫ t in x..y, g t ^ 2 := ⟨_, rfl⟩
  rw [← hS, ← hQ]
  rcases eq_or_lt_of_le hxy with h | h
  · subst h
    simp [hS]
  -- m = moyenne de g, et 0 ≤ ∫ (g - m)²
  obtain ⟨m, hm⟩ : ∃ m, m = S / (y - x) := ⟨_, rfl⟩
  have hmS : m * (y - x) = S := by rw [hm]; field_simp
  have h0 : 0 ≤ ∫ t in x..y, (g t - m) ^ 2 :=
    intervalIntegral.integral_nonneg hxy (fun t _ => sq_nonneg _)
  have e : ∫ t in x..y, (g t - m) ^ 2 = Q - 2 * m * S + m ^ 2 * (y - x) := by
    have hfun : (fun t => (g t - m) ^ 2) = fun t => g t ^ 2 - 2 * m * g t + m ^ 2 := by
      funext t
      ring
    rw [hfun, intervalIntegral.integral_add (hg2.sub (hg.const_mul (2 * m)))
      intervalIntegrable_const, intervalIntegral.integral_sub hg2 (hg.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul, ← hS,
      ← hQ]
    ring
  rw [e] at h0
  nlinarith

/-- **(C)** La minoration (2.1) uniforme : sur `[a,b] × [m₁, m₂]`, on a
`L(x,w,v) ≥ (μ/4) v² - K`. Seule la continuité de `L` est utilisée (pas celle de `L_v`). -/
lemma exists_lower_bound {a b m₁ m₂ : ℝ} {L : ℝ → ℝ → ℝ → ℝ}
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH2 : HypH2 a b L) :
    ∃ μ > 0, ∃ K, ∀ x ∈ Icc a b, ∀ w ∈ Icc m₁ m₂, ∀ v, μ / 4 * v ^ 2 - K ≤ L x w v := by
  obtain ⟨Lv, Lvv, μ, hμ, -, hH⟩ := hH2
  -- bornes de |L(x, w, c)| sur le compact [a,b] × [m₁, m₂]
  have hbound : ∀ c : ℝ, ∃ B, ∀ x ∈ Icc a b, ∀ w ∈ Icc m₁ m₂, |L x w c| ≤ B := by
    intro c
    have hK : IsCompact (Icc a b ×ˢ Icc m₁ m₂) := isCompact_Icc.prod isCompact_Icc
    have hmaps : MapsTo (fun p : ℝ × ℝ => (p.1, p.2, c)) (Icc a b ×ˢ Icc m₁ m₂)
        (Icc a b ×ˢ (univ : Set (ℝ × ℝ))) := fun p hp => ⟨hp.1, mem_univ _⟩
    have hc : ContinuousOn (fun p : ℝ × ℝ => L p.1 p.2 c) (Icc a b ×ˢ Icc m₁ m₂) :=
      hL.comp (by fun_prop) hmaps
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
    exact ⟨B, fun x hx w hw => by simpa using hB (x, w) ⟨hx, hw⟩⟩
  obtain ⟨B0, hB0⟩ := hbound 0
  obtain ⟨B1, hB1⟩ := hbound 1
  obtain ⟨Bm, hBm⟩ := hbound (-1)
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = |B0| + |B1| + |Bm| + μ := ⟨_, rfl⟩
  refine ⟨μ, hμ, C₀ + C₀ ^ 2 / μ, fun x hx w hw v => ?_⟩
  have h1 : ∀ v, HasDerivAt (fun v => L x w v) (Lv x w v) v := fun v => (hH x hx w v).1
  have h2 : ∀ v, HasDerivAt (fun v => Lv x w v) (Lvv x w v) v := fun v => (hH x hx w v).2.1
  have h3 : ∀ v, μ ≤ Lvv x w v := fun v => (hH x hx w v).2.2
  -- |L(x,w,0)| ≤ C₀ et |L_v(x,w,0)| ≤ C₀, par Taylor entre 0 et ±1
  have T1 := taylor_lower (φ := fun v => L x w v) (φd := fun v => Lv x w v) h1 h2 h3 0 1
  have T2 := taylor_lower (φ := fun v => L x w v) (φd := fun v => Lv x w v) h1 h2 h3 0 (-1)
  have a0 := hB0 x hx w hw
  have a1 := hB1 x hx w hw
  have am := hBm x hx w hw
  have b0 := le_abs_self B0
  have b1 := le_abs_self B1
  have bm := le_abs_self Bm
  have c0 := abs_le.mp a0
  have c1 := abs_le.mp a1
  have cm := abs_le.mp am
  have hC1 : |L x w 0| ≤ C₀ := by
    rw [abs_le]; constructor <;> linarith [abs_nonneg B1, abs_nonneg Bm]
  have hC2 : |Lv x w 0| ≤ C₀ := by
    rw [abs_le]; constructor <;> nlinarith
  have := lower_bound_L (φ := fun v => L x w v) (φd := fun v => Lv x w v) hμ h1 h2 h3 hC1 hC2 v
  linarith

/-! ## (2.2) et (2.3) : borne L² et caractère ½-höldérien -/

/-- Une fonction de `W^{1,1}([a,b])` est continue sur `[a,b]`. -/
lemma W11_continuousOn {u : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hu : IsW11 a b u) :
    ContinuousOn u (Icc a b) := by
  obtain ⟨g, hg, hrep⟩ := hu
  have hgI : IntegrableOn g (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hg
  have hc := intervalIntegral.continuousOn_primitive_interval hgI
  rw [uIcc_of_le hab] at hc
  exact (continuousOn_const.add hc).congr (fun x hx => hrep x hx)

/-- **(2.2) et (2.3)** : si `u ∈ W^{1,1}([a,b])` est d'énergie finie, alors `(u')²` est
intégrable sur `[a,b]` et `|u(y) - u(x)| ≤ N √(y - x)` avec `N = (∫ (u')²)^{1/2}`. -/
theorem holder_half {L : ℝ → ℝ → ℝ → ℝ} {u : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH2 : HypH2 a b L) (hu : IsW11 a b u) (hE : FiniteEnergy a b L u) :
    IntegrableOn (fun x => deriv u x ^ 2) (Icc a b) ∧
      ∃ N, 0 ≤ N ∧ ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
        |u y - u x| ≤ N * Real.sqrt (y - x) := by
  have hcont := W11_continuousOn hab hu
  obtain ⟨g, hg, hrep⟩ := hu
  -- u est bornée sur [a,b]
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Icc a b, |u x| ≤ M := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    exact ⟨M, fun x hx => by simpa using hM x hx⟩
  -- minoration (2.1) : (μ/4) (u')² ≤ L(x, u, u') + K
  obtain ⟨μ, hμ, K, hK⟩ := exists_lower_bound (m₁ := -M) (m₂ := M) hL hH2
  have hpt : ∀ x ∈ Icc a b, deriv u x ^ 2 ≤ 4 / μ * (L x (u x) (deriv u x) + K) := by
    intro x hx
    have := hK x hx (u x) (abs_le.mp (hM x hx)) (deriv u x)
    rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
    linarith
  -- (2.2) : (u')² est intégrable
  have hInt : IntegrableOn (fun x => deriv u x ^ 2) (Icc a b) := by
    refine Integrable.mono' ((hE.add (integrable_const K)).const_mul (4 / μ))
      ((measurable_deriv u).pow_const 2).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall (fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt x hx
  -- u' aussi, car |u'| ≤ (u')² + 1
  have hInt1 : IntegrableOn (deriv u) (Icc a b) := by
    refine Integrable.mono' (hInt.add (integrable_const 1))
      (measurable_deriv u).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall (fun x _ => ?_))
    rw [Real.norm_eq_abs]
    show |deriv u x| ≤ deriv u x ^ 2 + 1
    nlinarith [abs_nonneg (deriv u x), sq_abs (deriv u x), sq_nonneg (|deriv u x| - 1)]
  -- u(y) - u(x) = ∫ₓʸ u'
  have hae := W11_ae_hasDerivAt hab hg hrep
  have hrep2 : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → u y - u x = ∫ t in x..y, deriv u t := by
    intro x hx y hy hxy
    have hxI : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hx
    have hyI : y ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hy
    have h1 := intervalIntegral.integral_interval_sub_left
      (hg.mono_set (uIcc_subset_uIcc left_mem_uIcc hyI))
      (hg.mono_set (uIcc_subset_uIcc left_mem_uIcc hxI))
    have h2 : ∫ t in x..y, g t = ∫ t in x..y, deriv u t := by
      apply intervalIntegral.integral_congr_ae
      have hb : ∀ᵐ t : ℝ, t ≠ b := by simp [ae_iff, measure_singleton]
      filter_upwards [hae, hb] with t ht htb hmem
      rw [uIoc_of_le hxy] at hmem
      exact ((ht ⟨by linarith [hx.1, hmem.1], lt_of_le_of_ne (hmem.2.trans hy.2) htb⟩).deriv).symm
    rw [hrep y hy, hrep x hx]
    linarith
  -- (2.3) : Cauchy-Schwarz
  refine ⟨hInt, Real.sqrt (∫ t in Icc a b, deriv u t ^ 2), Real.sqrt_nonneg _,
    fun x hx y hy hxy => ?_⟩
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hii : IntervalIntegrable (deriv u) volume x y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr (hInt1.mono_set hsub)
  have hii2 : IntervalIntegrable (fun t => deriv u t ^ 2) volume x y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr (hInt.mono_set hsub)
  have hCS := sq_integral_le hxy hii hii2
  have hmono : ∫ t in x..y, deriv u t ^ 2 ≤ ∫ t in Icc a b, deriv u t ^ 2 := by
    rw [intervalIntegral.integral_of_le hxy]
    exact setIntegral_mono_set hInt (Eventually.of_forall (fun t => sq_nonneg _))
      ((Ioc_subset_Icc_self.trans hsub).eventuallyLE)
  rw [← hrep2 x hx y hy hxy] at hCS
  have h1 : (u y - u x) ^ 2 ≤ (y - x) * ∫ t in Icc a b, deriv u t ^ 2 :=
    hCS.trans (mul_le_mul_of_nonneg_left hmono (by linarith))
  calc |u y - u x| = Real.sqrt ((u y - u x) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((y - x) * ∫ t in Icc a b, deriv u t ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt (∫ t in Icc a b, deriv u t ^ 2) * Real.sqrt (y - x) := by
      rw [Real.sqrt_mul (by linarith), mul_comm]

/-! ## § 2.3 : les bons intervalles et l'inégalité (2.4) -/

lemma chord_of_mem {u : ℝ → ℝ} {σ τ x : ℝ} (hx : x ∈ Icc σ τ) :
    chord u σ τ x = u σ + slope u σ τ * (x - σ) := by
  simp only [chord, if_pos hx]

lemma chord_of_not_mem {u : ℝ → ℝ} {σ τ x : ℝ} (hx : x ∉ Icc σ τ) : chord u σ τ x = u x := by
  simp only [chord, if_neg hx]

lemma ae_ne_pt (c : ℝ) : ∀ᵐ t : ℝ, t ≠ c := by simp [ae_iff, measure_singleton]

/-- **L'inégalité (2.4)** : si `u` est une solution d'énergie finie et si `[σ,τ]` est bon
(la corde `u_{σ,τ}` reste entre les obstacles), alors
`∫_σ^τ L(x, u, u') ≤ ∫_σ^τ L(x, u_{σ,τ}, k(σ,τ))`. -/
theorem good_interval_ineq {L : ℝ → ℝ → ℝ → ℝ} {u f g : ℝ → ℝ} {a b A B σ τ : ℝ}
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hu : IsFiniteEnergySolution a b A B L f g u)
    (haσ : a ≤ σ) (hστ : σ < τ) (hτb : τ ≤ b)
    (hgood : ∀ x ∈ Icc σ τ, f x ≤ chord u σ τ x ∧ chord u σ τ x ≤ g x) :
    ∫ x in σ..τ, L x (u x) (deriv u x) ≤
      ∫ x in σ..τ, L x (u σ + slope u σ τ * (x - σ)) (slope u σ τ) := by
  obtain ⟨⟨hW, huA, huB, hfug⟩, hEu, hmin⟩ := hu
  have hab : a ≤ b := by linarith
  obtain ⟨G, hG, hrep⟩ := id hW
  obtain ⟨k, hk⟩ : ∃ k, slope u σ τ = k := ⟨_, rfl⟩
  rw [hk]
  have hkrel : (τ - σ) * k = u τ - u σ := by
    rw [← hk]
    simpa using sub_smul_slope u σ τ
  have hcin : ∀ x ∈ Icc σ τ, chord u σ τ x = u σ + k * (x - σ) := fun x hx => by
    rw [chord_of_mem hx, hk]
  have hcout : ∀ x ∉ Icc σ τ, chord u σ τ x = u x := fun x hx => chord_of_not_mem hx
  have hσab : σ ∈ Icc a b := ⟨haσ, by linarith⟩
  have hτab : τ ∈ Icc a b := ⟨by linarith, hτb⟩
  have haab : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbab : b ∈ Icc a b := ⟨hab, le_rfl⟩
  -- la fonction G̃ : k sur [σ,τ], G ailleurs
  obtain ⟨Gt, hGt⟩ : ∃ Gt : ℝ → ℝ, Gt = fun t => if t ∈ Icc σ τ then k else G t := ⟨_, rfl⟩
  have hGin : ∀ t ∈ Icc σ τ, Gt t = k := fun t ht => by rw [hGt]; simp only [if_pos ht]
  have hGout : ∀ t ∉ Icc σ τ, Gt t = G t := fun t ht => by rw [hGt]; simp only [if_neg ht]
  have hGsub : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, IntervalIntegrable G volume x y := by
    intro x hx y hy
    have hx' : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hx
    have hy' : y ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hy
    exact hG.mono_set (uIcc_subset_uIcc hx' hy')
  -- G̃ = G p.p. sur ]x,y] ⊂ [a,σ] ou ⊂ [τ,b], et G̃ = k sur ]x,y] ⊂ [σ,τ]
  have hGeq1 : ∀ x y, x ≤ y → y ≤ σ → ∀ᵐ t, t ∈ uIoc x y → G t = Gt t := by
    intro x y hxy hyσ
    filter_upwards [ae_ne_pt σ] with t ht hmem
    rw [uIoc_of_le hxy] at hmem
    exact (hGout t (fun hc => ht (le_antisymm (hmem.2.trans hyσ) hc.1))).symm
  have hGeq2 : ∀ x y, τ ≤ x → x ≤ y → ∀ᵐ t, t ∈ uIoc x y → G t = Gt t := by
    intro x y hτx hxy
    filter_upwards with t hmem
    rw [uIoc_of_le hxy] at hmem
    exact (hGout t (fun hc => by linarith [hc.2, hmem.1])).symm
  have hGeq3 : ∀ x y, σ ≤ x → x ≤ y → y ≤ τ →
      ∀ᵐ t, t ∈ uIoc x y → (fun _ : ℝ => k) t = Gt t := by
    intro x y hσx hxy hyτ
    filter_upwards with t hmem
    rw [uIoc_of_le hxy] at hmem
    exact (hGin t ⟨by linarith [hmem.1], hmem.2.trans hyτ⟩).symm
  -- intégrabilité de G̃ par morceaux
  have hiiGt1 : ∀ y, a ≤ y → y ≤ σ → IntervalIntegrable Gt volume a y := fun y hay hyσ =>
    (hGsub a haab y ⟨hay, by linarith⟩).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).mpr (hGeq1 a y hay hyσ))
  have hiiGt3 : ∀ y, σ ≤ y → y ≤ τ → IntervalIntegrable Gt volume σ y := fun y hσy hyτ =>
    (show IntervalIntegrable (fun _ : ℝ => k) volume σ y from intervalIntegrable_const).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).mpr (hGeq3 σ y le_rfl hσy hyτ))
  have hiiGt2 : ∀ y, τ ≤ y → y ≤ b → IntervalIntegrable Gt volume τ y := fun y hτy hyb =>
    (hGsub τ hτab y ⟨by linarith, hyb⟩).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).mpr (hGeq2 τ y le_rfl hτy))
  have hiiGaτ : IntervalIntegrable Gt volume a τ :=
    (hiiGt1 σ haσ le_rfl).trans (hiiGt3 τ hστ.le le_rfl)
  have hGtint : IntervalIntegrable Gt volume a b := hiiGaτ.trans (hiiGt2 b hτb le_rfl)
  -- intégrales de G̃ par morceaux
  have J1 : ∀ y, a ≤ y → y ≤ σ → ∫ t in a..y, Gt t = ∫ t in a..y, G t := fun y hay hyσ =>
    (intervalIntegral.integral_congr_ae (hGeq1 a y hay hyσ)).symm
  have J3 : ∀ y, σ ≤ y → y ≤ τ → ∫ t in σ..y, Gt t = (y - σ) * k := fun y hσy hyτ => by
    rw [← intervalIntegral.integral_congr_ae (hGeq3 σ y le_rfl hσy hyτ),
      intervalIntegral.integral_const, smul_eq_mul]
  have J2 : ∀ y, τ ≤ y → y ≤ b → ∫ t in τ..y, Gt t = ∫ t in τ..y, G t := fun y hτy hyb =>
    (intervalIntegral.integral_congr_ae (hGeq2 τ y le_rfl hτy)).symm
  -- la corde est dans W^{1,1}
  have hca : chord u σ τ a = u a := by
    by_cases ha : a ∈ Icc σ τ
    · rw [hcin a ha, show a = σ from le_antisymm haσ ha.1]
      ring
    · exact hcout a ha
  have hcb : chord u σ τ b = u b := by
    by_cases hb : b ∈ Icc σ τ
    · rw [hcin b hb, show b = τ from le_antisymm hb.2 hτb]
      linarith
    · exact hcout b hb
  have hrepc : ∀ x ∈ Icc a b, chord u σ τ x = chord u σ τ a + ∫ t in a..x, Gt t := by
    intro x hx
    rw [hca]
    have r1 := hrep σ hσab
    have r2 := hrep τ hτab
    have r3 := hrep x hx
    by_cases h1 : x < σ
    · rw [hcout x (fun h => by linarith [h.1]), J1 x hx.1 h1.le]
      exact r3
    · push Not at h1
      by_cases h2 : x ≤ τ
      · rw [hcin x ⟨h1, h2⟩]
        have e1 := intervalIntegral.integral_add_adjacent_intervals (hiiGt1 σ haσ le_rfl)
          (hiiGt3 x h1 h2)
        have e2 := J1 σ haσ le_rfl
        have e3 := J3 x h1 h2
        linarith
      · push Not at h2
        rw [hcout x (fun h => by linarith [h.2])]
        have e1 := intervalIntegral.integral_add_adjacent_intervals (hiiGt1 σ haσ le_rfl)
          (hiiGt3 τ hστ.le le_rfl)
        have e2 := intervalIntegral.integral_add_adjacent_intervals hiiGaτ
          (hiiGt2 x h2.le hx.2)
        have e3 := J1 σ haσ le_rfl
        have e4 := J3 τ hστ.le le_rfl
        have e5 := J2 x h2.le hx.2
        have f1 := intervalIntegral.integral_add_adjacent_intervals (hGsub a haab σ hσab)
          (hGsub σ hσab τ hτab)
        have f2 := intervalIntegral.integral_add_adjacent_intervals (hGsub a haab τ hτab)
          (hGsub τ hτab x hx)
        linarith
  have hWc : IsW11 a b (chord u σ τ) := ⟨Gt, hGtint, hrepc⟩
  -- dérivées presque partout
  have haeu := W11_ae_hasDerivAt hab hG hrep
  have haec := W11_ae_hasDerivAt hab hGtint hrepc
  -- la corde est admissible
  have hAc : chord u σ τ ∈ Admissible a b A B f g := by
    refine ⟨hWc, by rw [hca]; exact huA, by rw [hcb]; exact huB, fun x hx => ?_⟩
    by_cases hxin : x ∈ Icc σ τ
    · exact hgood x hxin
    · rw [hcout x hxin]
      exact hfug x hx
  -- densités d'énergie : égales hors de [σ,τ], égales à L(x, corde, k) dans ]σ,τ[
  have hdens_out : ∀ x, x ∈ Ioo a b → x ∉ Icc σ τ →
      (x ∈ Ioo a b → HasDerivAt u (G x) x) →
      (x ∈ Ioo a b → HasDerivAt (chord u σ τ) (Gt x) x) →
      energyDensity L u x = energyDensity L (chord u σ τ) x := by
    intro x hxI hxout h1 h2
    simp only [energyDensity]
    rw [(h1 hxI).deriv, (h2 hxI).deriv, hGout x hxout, hcout x hxout]
  have hdens_in : ∀ x, x ∈ Ioo a b → x ∈ Icc σ τ →
      (x ∈ Ioo a b → HasDerivAt (chord u σ τ) (Gt x) x) →
      energyDensity L (chord u σ τ) x = L x (u σ + k * (x - σ)) k := by
    intro x hxI hxin h2
    simp only [energyDensity]
    rw [(h2 hxI).deriv, hGin x hxin, hcin x hxin]
  -- la corde est d'énergie finie
  have hcont : ContinuousOn (fun x => L x (u σ + k * (x - σ)) k) (Icc σ τ) := by
    have hmaps : MapsTo (fun x : ℝ => (x, u σ + k * (x - σ), k)) (Icc σ τ)
        (Icc a b ×ˢ (univ : Set (ℝ × ℝ))) :=
      fun x hx => ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, mem_univ _⟩
    exact hL.comp (by fun_prop) hmaps
  have hEc : FiniteEnergy a b L (chord u σ τ) := by
    unfold FiniteEnergy
    rw [← Icc_union_Icc_eq_Icc haσ (show σ ≤ b by linarith), ← Icc_union_Icc_eq_Icc hστ.le hτb]
    refine IntegrableOn.union ?_ (IntegrableOn.union ?_ ?_)
    · refine (hEu.mono_set (Icc_subset_Icc le_rfl (show σ ≤ b by linarith))).congr_fun_ae ?_
      refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
      filter_upwards [haeu, haec, ae_ne_pt a, ae_ne_pt σ] with x h1 h2 h3 h4 hx
      have hxσ : x < σ := lt_of_le_of_ne hx.2 h4
      exact hdens_out x ⟨lt_of_le_of_ne hx.1 (Ne.symm h3), by linarith⟩
        (fun h => by linarith [h.1]) h1 h2
    · refine hcont.integrableOn_Icc.congr_fun_ae ?_
      refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
      filter_upwards [haec, ae_ne_pt σ, ae_ne_pt τ] with x h2 h3 h4 hx
      have hσx : σ < x := lt_of_le_of_ne hx.1 (Ne.symm h3)
      have hxτ : x < τ := lt_of_le_of_ne hx.2 h4
      exact (hdens_in x ⟨by linarith, by linarith⟩ hx h2).symm
    · refine (hEu.mono_set (Icc_subset_Icc (show a ≤ τ by linarith) le_rfl)).congr_fun_ae ?_
      refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
      filter_upwards [haeu, haec, ae_ne_pt τ, ae_ne_pt b] with x h1 h2 h3 h4 hx
      have hτx : τ < x := lt_of_le_of_ne hx.1 (Ne.symm h3)
      exact hdens_out x ⟨by linarith, lt_of_le_of_ne hx.2 h4⟩
        (fun h => by linarith [h.2]) h1 h2
  -- minimalité, puis découpage de l'énergie en trois morceaux
  have hmin' := hmin (chord u σ τ) hAc hEc
  unfold energy at hmin'
  have hiiU : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      IntervalIntegrable (energyDensity L u) volume x y := fun x hx y hy hxy =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr
      (hEu.mono_set (Icc_subset_Icc hx.1 hy.2))
  have hiiC : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      IntervalIntegrable (energyDensity L (chord u σ τ)) volume x y := fun x hx y hy hxy =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr
      (hEc.mono_set (Icc_subset_Icc hx.1 hy.2))
  have sU1 := intervalIntegral.integral_add_adjacent_intervals (hiiU a haab σ hσab haσ)
    (hiiU σ hσab τ hτab hστ.le)
  have sU2 := intervalIntegral.integral_add_adjacent_intervals (hiiU a haab τ hτab (by linarith))
    (hiiU τ hτab b hbab hτb)
  have sC1 := intervalIntegral.integral_add_adjacent_intervals (hiiC a haab σ hσab haσ)
    (hiiC σ hσab τ hτab hστ.le)
  have sC2 := intervalIntegral.integral_add_adjacent_intervals (hiiC a haab τ hτab (by linarith))
    (hiiC τ hτab b hbab hτb)
  have eq1 : ∫ x in a..σ, energyDensity L u x = ∫ x in a..σ, energyDensity L (chord u σ τ) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [haeu, haec, ae_ne_pt σ] with x h1 h2 h4 hmem
    rw [uIoc_of_le haσ] at hmem
    have hxσ : x < σ := lt_of_le_of_ne hmem.2 h4
    exact hdens_out x ⟨hmem.1, by linarith⟩ (fun h => by linarith [h.1]) h1 h2
  have eq3 : ∫ x in τ..b, energyDensity L u x = ∫ x in τ..b, energyDensity L (chord u σ τ) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [haeu, haec, ae_ne_pt b] with x h1 h2 h4 hmem
    rw [uIoc_of_le hτb] at hmem
    exact hdens_out x ⟨by linarith [hmem.1], lt_of_le_of_ne hmem.2 h4⟩
      (fun h => by linarith [h.2, hmem.1]) h1 h2
  have eqmid : ∫ x in σ..τ, energyDensity L (chord u σ τ) x =
      ∫ x in σ..τ, L x (u σ + k * (x - σ)) k := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [haec, ae_ne_pt τ] with x h2 h4 hmem
    rw [uIoc_of_le hστ.le] at hmem
    have hxτ : x < τ := lt_of_le_of_ne hmem.2 h4
    exact hdens_in x ⟨by linarith [hmem.1], by linarith⟩ ⟨hmem.1.le, hmem.2⟩ h2
  show ∫ x in σ..τ, energyDensity L u x ≤ _
  linarith

/-! ## Lemme 2.6, étapes 1 et 2 : inégalités ponctuelles -/

/-- **Taylor minorée locale** : si `μ ≤ φ''` sur `[m, M]`, alors pour `v₀, v ∈ [m, M]`,
`φ(v) ≥ φ(v₀) + φ'(v₀)(v - v₀) + (μ/2)(v - v₀)²`. -/
lemma taylor_lower_on {φ φd φdd : ℝ → ℝ} {μ m M : ℝ} (h1 : ∀ v, HasDerivAt φ (φd v) v)
    (h2 : ∀ v, HasDerivAt φd (φdd v) v) (hμ : ∀ v ∈ Icc m M, μ ≤ φdd v) {v₀ v : ℝ}
    (hv₀ : v₀ ∈ Icc m M) (hv : v ∈ Icc m M) :
    φ v₀ + φd v₀ * (v - v₀) + μ / 2 * ((v - v₀) * (v - v₀)) ≤ φ v := by
  have hg1 : ∀ y, HasDerivAt (fun y => φd y - μ * y) (φdd y - μ * 1) y := fun y =>
    (h2 y).sub ((hasDerivAt_id' y).const_mul μ)
  have hmono : MonotoneOn (fun y => φd y - μ * y) (Icc m M) :=
    monotoneOn_of_deriv_nonneg (convex_Icc m M)
      (fun y _ => (hg1 y).continuousAt.continuousWithinAt)
      (fun y _ => (hg1 y).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [interior_Icc] at hy
        rw [(hg1 y).deriv]
        linarith [hμ y (Ioo_subset_Icc_self hy)])
  have hψ : ∀ y, HasDerivAt (fun y => φ y - φd v₀ * y - μ / 2 * ((y - v₀) * (y - v₀)))
      (φd y - φd v₀ - μ * (y - v₀)) y := fun y =>
    (((h1 y).sub ((hasDerivAt_id' y).const_mul (φd v₀))).sub
      ((((hasDerivAt_id' y).sub_const v₀).mul ((hasDerivAt_id' y).sub_const v₀)).const_mul
        (μ / 2))).congr_deriv (by ring)
  have hcont : ∀ a b, ContinuousOn
      (fun y => φ y - φd v₀ * y - μ / 2 * ((y - v₀) * (y - v₀))) (Icc a b) :=
    fun a b x _ => (hψ x).continuousAt.continuousWithinAt
  rcases lt_trichotomy v v₀ with hv' | hv' | hv'
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope _ _ hv' (hcont v v₀) (fun x _ => hψ x)
    have hξI : ξ ∈ Icc m M := ⟨by linarith [hv.1, hξ.1], by linarith [hv₀.2, hξ.2]⟩
    have hm : φd ξ - μ * ξ ≤ φd v₀ - μ * v₀ := hmono hξI hv₀ hξ.2.le
    rw [eq_div_iff (sub_ne_zero.mpr hv'.ne')] at hξeq
    have := mul_le_mul_of_nonneg_right
      (show φd ξ - φd v₀ - μ * (ξ - v₀) ≤ 0 by linarith) (show (0 : ℝ) ≤ v₀ - v by linarith)
    linarith
  · subst hv'
    simp
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope _ _ hv' (hcont v₀ v) (fun x _ => hψ x)
    have hξI : ξ ∈ Icc m M := ⟨by linarith [hv₀.1, hξ.1], by linarith [hv.2, hξ.2]⟩
    have hm : φd v₀ - μ * v₀ ≤ φd ξ - μ * ξ := hmono hv₀ hξI hξ.1.le
    rw [eq_div_iff (sub_ne_zero.mpr hv'.ne')] at hξeq
    have := mul_le_mul_of_nonneg_right
      (show 0 ≤ φd ξ - φd v₀ - μ * (ξ - v₀) by linarith) (show (0 : ℝ) ≤ v - v₀ by linarith)
    linarith

/-- **Taylor majorée locale** : si `φ'' ≤ Λ` sur `[m, M]`, alors pour `v₀, v ∈ [m, M]`,
`φ(v) ≤ φ(v₀) + φ'(v₀)(v - v₀) + (Λ/2)(v - v₀)²`. -/
lemma taylor_upper_on {φ φd φdd : ℝ → ℝ} {Λ m M : ℝ} (h1 : ∀ v, HasDerivAt φ (φd v) v)
    (h2 : ∀ v, HasDerivAt φd (φdd v) v) (hΛ : ∀ v ∈ Icc m M, φdd v ≤ Λ) {v₀ v : ℝ}
    (hv₀ : v₀ ∈ Icc m M) (hv : v ∈ Icc m M) :
    φ v ≤ φ v₀ + φd v₀ * (v - v₀) + Λ / 2 * ((v - v₀) * (v - v₀)) := by
  have := taylor_lower_on (φ := fun v => -φ v) (φd := fun v => -φd v) (φdd := fun v => -φdd v)
    (μ := -Λ) (fun v => (h1 v).neg) (fun v => (h2 v).neg)
    (fun v hv => by linarith [hΛ v hv]) hv₀ hv
  linarith

/-- **Étape 1, forme abstraite** : si `|φ - ψ| ≤ D` en `v` et `v + h`, et si
`μ ≤ φ'', ψ'' ≤ Λ` sur `[v, v + h]`, alors `h |φ'(v) - ψ'(v)| ≤ 2D + Λ h²`. -/
lemma deriv_diff_bound {φ φd φdd ψ ψd ψdd : ℝ → ℝ} {v h D μ Λ : ℝ} (hh : 0 < h)
    (hμ0 : 0 ≤ μ)
    (hφ1 : ∀ s, HasDerivAt φ (φd s) s) (hφ2 : ∀ s, HasDerivAt φd (φdd s) s)
    (hψ1 : ∀ s, HasDerivAt ψ (ψd s) s) (hψ2 : ∀ s, HasDerivAt ψd (ψdd s) s)
    (hφb : ∀ s ∈ Icc v (v + h), μ ≤ φdd s ∧ φdd s ≤ Λ)
    (hψb : ∀ s ∈ Icc v (v + h), μ ≤ ψdd s ∧ ψdd s ≤ Λ)
    (hD0 : |φ v - ψ v| ≤ D) (hD1 : |φ (v + h) - ψ (v + h)| ≤ D) :
    h * |φd v - ψd v| ≤ 2 * D + Λ * h ^ 2 := by
  have hv : v ∈ Icc v (v + h) := ⟨le_rfl, by linarith⟩
  have hvh : v + h ∈ Icc v (v + h) := ⟨by linarith, le_rfl⟩
  have Lφ := taylor_lower_on hφ1 hφ2 (fun s hs => (hφb s hs).1) hv hvh
  have Uφ := taylor_upper_on hφ1 hφ2 (fun s hs => (hφb s hs).2) hv hvh
  have Lψ := taylor_lower_on hψ1 hψ2 (fun s hs => (hψb s hs).1) hv hvh
  have Uψ := taylor_upper_on hψ1 hψ2 (fun s hs => (hψb s hs).2) hv hvh
  have e : v + h - v = h := by ring
  rw [e] at Lφ Uφ Lψ Uψ
  have hΛ : 0 ≤ Λ := le_trans hμ0 ((hφb v hv).1.trans (hφb v hv).2)
  have a0 := abs_le.mp hD0
  have a1 := abs_le.mp hD1
  have p1 := mul_nonneg hμ0 (mul_self_nonneg h)
  have p2 := mul_nonneg hΛ (mul_self_nonneg h)
  rcases abs_cases (φd v - ψd v) with ⟨habs, _⟩ | ⟨habs, _⟩
  · rw [habs]
    nlinarith
  · rw [habs]
    nlinarith

/-- **Étape 2, forme abstraite** : avec `ζ = u' - k`, si
`F₁ = L(x,u,k+ζ) - L(x,u,k) - L_v(x,u,k) ζ ≥ (μ/2) ζ²`, `|L_v(x,u,k) - p̄| ≤ A` et
`|L(x,u,k) - L(x,c,k)| ≤ B`, alors `F = L(x,u,u') - L(x,c,k) - p̄ ζ ≥ (μ/4) ζ² - A²/μ - B`. -/
lemma pointwise_F {Lu0 Lc0 Luu Lvk pbar ζ μ A B : ℝ} (hμ : 0 < μ)
    (hF1 : Lu0 + Lvk * ζ + μ / 2 * (ζ * ζ) ≤ Luu) (hF2 : |Lvk - pbar| ≤ A)
    (hF3 : |Lu0 - Lc0| ≤ B) :
    μ / 4 * ζ ^ 2 - A ^ 2 / μ - B ≤ Luu - Lc0 - pbar * ζ := by
  have hA : 0 ≤ A := (abs_nonneg _).trans hF2
  -- (L_v - p̄) ζ ≥ -A |ζ|
  have h2 : -(A * |ζ|) ≤ (Lvk - pbar) * ζ := by
    have h3 := neg_abs_le ((Lvk - pbar) * ζ)
    rw [abs_mul] at h3
    have h4 := mul_le_mul_of_nonneg_right hF2 (abs_nonneg ζ)
    linarith
  -- Young : A |ζ| ≤ (μ/4) ζ² + A²/μ
  have hY : A * |ζ| ≤ μ / 4 * ζ ^ 2 + A ^ 2 / μ := by
    have e : μ / 4 * ζ ^ 2 + A ^ 2 / μ - A * |ζ| = (μ * |ζ| - 2 * A) ^ 2 / (4 * μ) := by
      rw [← sq_abs ζ]
      field_simp
      ring
    have : 0 ≤ (μ * |ζ| - 2 * A) ^ 2 / (4 * μ) := by positivity
    linarith
  have h5 := (abs_le.mp hF3).1
  nlinarith [sq_nonneg ζ]

/-! ## Lemme 2.6 : l'inégalité (2.5) et l'étape 3 -/

/-- **(2.5)** : `L_v` est höldérienne d'exposant `α/2` en `(x,w)`. Si `L` est
`C`-`α`-höldérienne en `(x,w)` sur `[v, v + 1]` et si `μ ≤ L_vv ≤ Λ` sur `[v, v + 1]`, alors
`|L_v(P,v) - L_v(P',v)| ≤ (2C + Λ) d^{α/2}` pour `d = |x₁ - x₂| + |w₁ - w₂| ≤ 1`. -/
lemma Lv_holder {L Lv Lvv : ℝ → ℝ → ℝ → ℝ} {x₁ w₁ x₂ w₂ v C α μ Λ : ℝ}
    (hμ0 : 0 ≤ μ) (hα : 0 < α) (hC : 0 ≤ C) (hd1 : |x₁ - x₂| + |w₁ - w₂| ≤ 1)
    (hφ1 : ∀ s, HasDerivAt (fun s => L x₁ w₁ s) (Lv x₁ w₁ s) s)
    (hφ2 : ∀ s, HasDerivAt (fun s => Lv x₁ w₁ s) (Lvv x₁ w₁ s) s)
    (hψ1 : ∀ s, HasDerivAt (fun s => L x₂ w₂ s) (Lv x₂ w₂ s) s)
    (hψ2 : ∀ s, HasDerivAt (fun s => Lv x₂ w₂ s) (Lvv x₂ w₂ s) s)
    (hb1 : ∀ s ∈ Icc v (v + 1), μ ≤ Lvv x₁ w₁ s ∧ Lvv x₁ w₁ s ≤ Λ)
    (hb2 : ∀ s ∈ Icc v (v + 1), μ ≤ Lvv x₂ w₂ s ∧ Lvv x₂ w₂ s ≤ Λ)
    (hH : ∀ s ∈ Icc v (v + 1),
      |L x₁ w₁ s - L x₂ w₂ s| ≤ C * (|x₁ - x₂| + |w₁ - w₂|) ^ α) :
    |Lv x₁ w₁ v - Lv x₂ w₂ v| ≤ (2 * C + Λ) * (|x₁ - x₂| + |w₁ - w₂|) ^ (α / 2) := by
  obtain ⟨d, hd⟩ : ∃ d, d = |x₁ - x₂| + |w₁ - w₂| := ⟨_, rfl⟩
  rw [← hd] at hd1 hH ⊢
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have hΛ : 0 ≤ Λ := le_trans hμ0 ((hb1 v ⟨le_rfl, by linarith⟩).1.trans
    (hb1 v ⟨le_rfl, by linarith⟩).2)
  rcases eq_or_lt_of_le hd0 with h0 | hdpos
  · -- d = 0 : les deux points coïncident
    have hx : x₁ = x₂ := by
      have := abs_nonneg (x₁ - x₂)
      have := abs_nonneg (w₁ - w₂)
      have h1 : |x₁ - x₂| = 0 := by linarith
      exact sub_eq_zero.mp (abs_eq_zero.mp h1)
    have hw : w₁ = w₂ := by
      have := abs_nonneg (x₁ - x₂)
      have := abs_nonneg (w₁ - w₂)
      have h1 : |w₁ - w₂| = 0 := by linarith
      exact sub_eq_zero.mp (abs_eq_zero.mp h1)
    subst hx hw
    simp only [sub_self, abs_zero]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hd0 _)
  · -- d > 0 : h = d^{α/2} ∈ ]0, 1], et h² = d^α
    obtain ⟨h, hh⟩ : ∃ h, h = d ^ (α / 2) := ⟨_, rfl⟩
    have hhpos : 0 < h := by rw [hh]; exact Real.rpow_pos_of_pos hdpos _
    have hh1 : h ≤ 1 := by rw [hh]; exact Real.rpow_le_one hd0 hd1 (by linarith)
    have hh2 : h ^ 2 = d ^ α := by
      rw [hh, ← Real.rpow_natCast, ← Real.rpow_mul hd0]
      congr 1
      push_cast
      ring
    rw [← hh]
    have key := deriv_diff_bound (φ := fun s => L x₁ w₁ s) (φd := fun s => Lv x₁ w₁ s)
      (φdd := fun s => Lvv x₁ w₁ s) (ψ := fun s => L x₂ w₂ s) (ψd := fun s => Lv x₂ w₂ s)
      (ψdd := fun s => Lvv x₂ w₂ s) (v := v) (h := h) (D := C * d ^ α) (μ := μ) (Λ := Λ)
      hhpos hμ0 hφ1 hφ2 hψ1 hψ2
      (fun s hs => hb1 s ⟨hs.1, by linarith [hs.2]⟩)
      (fun s hs => hb2 s ⟨hs.1, by linarith [hs.2]⟩)
      (hH v ⟨le_rfl, by linarith⟩) (hH (v + h) ⟨by linarith, by linarith⟩)
    rw [← hh2] at key
    have : h * |Lv x₁ w₁ v - Lv x₂ w₂ v| ≤ h * ((2 * C + Λ) * h) := by nlinarith
    exact le_of_mul_le_mul_left this hhpos

open MeasureTheory in
/-- **Étape 3, forme abstraite** : intégration de la borne ponctuelle de l'étape 2. -/
lemma integral_step {Fu Fc ζ : ℝ → ℝ} {σ τ pbar μ A B : ℝ} (hστ : σ ≤ τ) (_hμ : 0 < μ)
    (hFu : IntervalIntegrable Fu volume σ τ) (hFc : IntervalIntegrable Fc volume σ τ)
    (hζ : IntervalIntegrable ζ volume σ τ)
    (hζ2 : IntervalIntegrable (fun x => ζ x ^ 2) volume σ τ)
    (h24 : ∫ x in σ..τ, Fu x ≤ ∫ x in σ..τ, Fc x) (hζ0 : ∫ x in σ..τ, ζ x = 0)
    (hpt : ∀ᵐ x, x ∈ Ioo σ τ → μ / 4 * ζ x ^ 2 - A ^ 2 / μ - B ≤ Fu x - Fc x - pbar * ζ x) :
    μ / 4 * ∫ x in σ..τ, ζ x ^ 2 ≤ (A ^ 2 / μ + B) * (τ - σ) := by
  have hl1 : IntervalIntegrable (fun x => μ / 4 * ζ x ^ 2 - A ^ 2 / μ) volume σ τ :=
    (hζ2.const_mul (μ / 4)).sub intervalIntegrable_const
  have hl : IntervalIntegrable (fun x => μ / 4 * ζ x ^ 2 - A ^ 2 / μ - B) volume σ τ :=
    hl1.sub intervalIntegrable_const
  have hr1 : IntervalIntegrable (fun x => Fu x - Fc x) volume σ τ := hFu.sub hFc
  have hr : IntervalIntegrable (fun x => Fu x - Fc x - pbar * ζ x) volume σ τ :=
    hr1.sub (hζ.const_mul pbar)
  have hmono := intervalIntegral.integral_mono_ae_restrict hστ hl hr
    ((ae_restrict_iff' measurableSet_Icc).mpr (by
      filter_upwards [hpt, ae_ne_pt σ, ae_ne_pt τ] with x h h1 h2 hx
      exact h ⟨lt_of_le_of_ne hx.1 (Ne.symm h1), lt_of_le_of_ne hx.2 h2⟩))
  have e1 : ∫ x in σ..τ, (μ / 4 * ζ x ^ 2 - A ^ 2 / μ - B) =
      μ / 4 * (∫ x in σ..τ, ζ x ^ 2) - (τ - σ) * (A ^ 2 / μ) - (τ - σ) * B := by
    rw [intervalIntegral.integral_sub hl1 intervalIntegrable_const,
      intervalIntegral.integral_sub (hζ2.const_mul (μ / 4)) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
  have e2 : ∫ x in σ..τ, (Fu x - Fc x - pbar * ζ x) =
      (∫ x in σ..τ, Fu x) - (∫ x in σ..τ, Fc x) - pbar * ∫ x in σ..τ, ζ x := by
    rw [intervalIntegral.integral_sub hr1 (hζ.const_mul pbar),
      intervalIntegral.integral_sub hFu hFc, intervalIntegral.integral_const_mul]
  rw [e1, e2, hζ0] at hmono
  nlinarith

/-! ## Lemme 2.6 : l'estimation de base -/

open MeasureTheory in
/-- `u'` est intégrable et `u(y) - u(x) = ∫ₓʸ u'`, pour `u ∈ W^{1,1}` d'énergie finie. -/
theorem W11_deriv_facts {L : ℝ → ℝ → ℝ → ℝ} {u : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH2 : HypH2 a b L) (hu : IsW11 a b u) (hE : FiniteEnergy a b L u) :
    IntegrableOn (deriv u) (Icc a b) ∧
      ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → u y - u x = ∫ t in x..y, deriv u t := by
  obtain ⟨hInt, -⟩ := holder_half hab hL hH2 hu hE
  have hInt1 : IntegrableOn (deriv u) (Icc a b) := by
    refine Integrable.mono' (hInt.add (integrable_const 1))
      (measurable_deriv u).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall (fun x _ => ?_))
    rw [Real.norm_eq_abs]
    show |deriv u x| ≤ deriv u x ^ 2 + 1
    nlinarith [abs_nonneg (deriv u x), sq_abs (deriv u x), sq_nonneg (|deriv u x| - 1)]
  refine ⟨hInt1, ?_⟩
  obtain ⟨g, hg, hrep⟩ := hu
  have hae := W11_ae_hasDerivAt hab hg hrep
  intro x hx y hy hxy
  have hxI : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hx
  have hyI : y ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hy
  have h1 := intervalIntegral.integral_interval_sub_left
    (hg.mono_set (uIcc_subset_uIcc left_mem_uIcc hyI))
    (hg.mono_set (uIcc_subset_uIcc left_mem_uIcc hxI))
  have h2 : ∫ t in x..y, g t = ∫ t in x..y, deriv u t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae, ae_ne_pt b] with t ht htb hmem
    rw [uIoc_of_le hxy] at hmem
    exact ((ht ⟨by linarith [hx.1, hmem.1], lt_of_le_of_ne (hmem.2.trans hy.2) htb⟩).deriv).symm
  rw [hrep y hy, hrep x hx]
  linarith

open MeasureTheory in
/-- **Lemme 2.6** (estimation de base sur les bons intervalles) : pour `K ≥ 0`, il existe `C`
et `γ > 0` tels que, pour tout bon intervalle `[σ,τ]` avec `ε + N√ε ≤ 1` (`ε = τ - σ`) et
`|k(σ,τ)| ≤ K`, on a `(1/ε) ∫_σ^τ |u' - k(σ,τ)|² ≤ C ε^γ`. -/
theorem basic_estimate {L : ℝ → ℝ → ℝ → ℝ} {u f g : ℝ → ℝ} {a b A B : ℝ} (hab : a ≤ b)
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH1 : HypH1 a b L) (hH2 : HypH2 a b L) (hu : IsFiniteEnergySolution a b A B L f g u)
    {N : ℝ} (hN0 : 0 ≤ N)
    (hN : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |u y - u x| ≤ N * Real.sqrt (y - x))
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ C γ : ℝ, 0 < γ ∧ ∀ σ τ, a ≤ σ → σ < τ → τ ≤ b → (1 + N) * Real.sqrt (τ - σ) ≤ 1 →
      (∀ x ∈ Icc σ τ, f x ≤ chord u σ τ x ∧ chord u σ τ x ≤ g x) → |slope u σ τ| ≤ K →
      (∫ x in σ..τ, (deriv u x - slope u σ τ) ^ 2) / (τ - σ) ≤ C * (τ - σ) ^ γ := by
  have hu' := hu
  obtain ⟨⟨hW, -, -, -⟩, hE, -⟩ := hu'
  obtain ⟨hInt, -⟩ := holder_half hab hL hH2 hW hE
  obtain ⟨hInt1, hrep2⟩ := W11_deriv_facts hab hL hH2 hW hE
  have hcont := W11_continuousOn hab hW
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Icc a b, |u x| ≤ M := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    exact ⟨M, fun x hx => by simpa using hM x hx⟩
  obtain ⟨R, hR⟩ : ∃ R, R = M + K + 2 := ⟨_, rfl⟩
  obtain ⟨C, hC, α, hα, hα1, hH⟩ := hH1 R
  obtain ⟨Lv, Lvv, μ, hμ, hLvv, hD⟩ := hH2
  -- Λ = max L_vv sur le compact [a,b] × [-R,R] × [-R,R]
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, ∀ x ∈ Icc a b, ∀ w ∈ Icc (-R) R, ∀ v ∈ Icc (-R) R, Lvv x w v ≤ Λ := by
    have hKc : IsCompact (Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)) :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    obtain ⟨Λ, hΛ⟩ :=
      hKc.exists_bound_of_continuousOn (hLvv.mono (prod_mono subset_rfl (subset_univ _)))
    exact ⟨Λ, fun x hx w hw v hv =>
      le_trans (le_abs_self _) (by simpa using hΛ (x, w, v) ⟨hx, hw, hv⟩)⟩
  refine ⟨4 / μ * ((2 * C + Λ) ^ 2 * (1 + N) / μ + C * (1 + 2 * N)), α / 2, by linarith, ?_⟩
  intro σ τ haσ hστ hτb hε hgood hk
  obtain ⟨ε, hε_def⟩ : ∃ ε, ε = τ - σ := ⟨_, rfl⟩
  rw [← hε_def] at hε ⊢
  have hεpos : 0 < ε := by rw [hε_def]; linarith
  have hsq1 : Real.sqrt ε ≤ 1 := by
    have := Real.sqrt_nonneg ε
    nlinarith [mul_nonneg hN0 this]
  have hNsq : N * Real.sqrt ε ≤ 1 := by
    have := Real.sqrt_nonneg ε
    nlinarith
  have hεsq : ε ≤ Real.sqrt ε := by
    have h1 := Real.mul_self_sqrt hεpos.le
    have h2 := Real.sqrt_nonneg ε
    nlinarith
  obtain ⟨k, hk_def⟩ : ∃ k, slope u σ τ = k := ⟨_, rfl⟩
  rw [hk_def] at hk ⊢
  have hkrel : ε * k = u τ - u σ := by
    rw [hε_def, ← hk_def]
    simpa using sub_smul_slope u σ τ
  have hσab : σ ∈ Icc a b := ⟨haσ, by linarith⟩
  have hτab : τ ∈ Icc a b := ⟨by linarith, hτb⟩
  have hsub : Icc σ τ ⊆ Icc a b := Icc_subset_Icc haσ hτb
  have hkK := abs_le.mp hk
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM σ hσab)
  -- estimations de base sur [σ,τ]
  have hdiffσ : ∀ x ∈ Icc σ τ, |u x - u σ| ≤ N * Real.sqrt ε := fun x hx =>
    (hN σ hσab x (hsub hx) hx.1).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [hx.2])) hN0)
  have hcσ : ∀ x ∈ Icc σ τ, |u σ + k * (x - σ) - u σ| ≤ N * Real.sqrt ε := by
    intro x hx
    rw [show u σ + k * (x - σ) - u σ = k * (x - σ) by ring, abs_mul,
      abs_of_nonneg (show 0 ≤ x - σ by linarith [hx.1])]
    have h1 : |k| * (x - σ) ≤ |k| * ε := mul_le_mul_of_nonneg_left (by linarith [hx.2])
      (abs_nonneg k)
    have h2 : |k| * ε = |u τ - u σ| := by rw [← hkrel, abs_mul, abs_of_pos hεpos, mul_comm]
    have h3 := hdiffσ τ ⟨hστ.le, le_rfl⟩
    linarith
  have hRu : ∀ x ∈ Icc σ τ, u x ∈ Icc (-R) R := fun x hx => by
    have := abs_le.mp (hM x (hsub hx))
    exact ⟨by linarith, by linarith⟩
  have hRc : ∀ x ∈ Icc σ τ, u σ + k * (x - σ) ∈ Icc (-R) R := fun x hx => by
    have h1 := abs_le.mp (hcσ x hx)
    have h2 := abs_le.mp (hM σ hσab)
    exact ⟨by linarith, by linarith⟩
  have hRs : ∀ s ∈ Icc k (k + 1), s ∈ Icc (-R) R := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hRk : k ∈ Icc (-R) R := hRs k ⟨le_rfl, by linarith⟩
  -- les quantités A et B
  obtain ⟨A', hA'⟩ : ∃ A', A' = (2 * C + Λ) * ((1 + N) * Real.sqrt ε) ^ (α / 2) := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B', B' = C * (2 * N * Real.sqrt ε) ^ α := ⟨_, rfl⟩
  have hΛμ : μ ≤ Λ := (hD σ hσab (u σ) k).2.2.trans (hΛ σ hσab (u σ) (hRu σ ⟨le_rfl, hστ.le⟩) k hRk)
  -- étape 2 : la borne ponctuelle
  have hpt : ∀ x ∈ Icc σ τ, μ / 4 * (deriv u x - k) ^ 2 - A' ^ 2 / μ - B' ≤
      L x (u x) (deriv u x) - L x (u σ + k * (x - σ)) k - Lv σ (u σ) k * (deriv u x - k) := by
    intro x hx
    have hxab := hsub hx
    -- F₁ (Taylor en v, au point k)
    have hF1 := taylor_lower (φ := fun v => L x (u x) v) (φd := fun v => Lv x (u x) v)
      (φdd := fun v => Lvv x (u x) v) (fun v => (hD x hxab (u x) v).1)
      (fun v => (hD x hxab (u x) v).2.1) (fun v => (hD x hxab (u x) v).2.2) k (deriv u x)
    -- F₂ : Hölder de L_v (2.5)
    have hd : |x - σ| + |u x - u σ| ≤ (1 + N) * Real.sqrt ε := by
      rw [abs_of_nonneg (show 0 ≤ x - σ by linarith [hx.1])]
      have := hdiffσ x hx
      nlinarith [hx.2]
    have hd1 : |x - σ| + |u x - u σ| ≤ 1 := hd.trans hε
    have hF2' := Lv_holder (L := L) (Lv := Lv) (Lvv := Lvv) (x₁ := x) (w₁ := u x) (x₂ := σ)
      (w₂ := u σ) (v := k) (C := C) (α := α) (μ := μ) (Λ := Λ) hμ.le hα hC.le hd1
      (fun s => (hD x hxab (u x) s).1) (fun s => (hD x hxab (u x) s).2.1)
      (fun s => (hD σ hσab (u σ) s).1) (fun s => (hD σ hσab (u σ) s).2.1)
      (fun s hs => ⟨(hD x hxab (u x) s).2.2, hΛ x hxab (u x) (hRu x hx) s (hRs s hs)⟩)
      (fun s hs => ⟨(hD σ hσab (u σ) s).2.2,
        hΛ σ hσab (u σ) (hRu σ ⟨le_rfl, hστ.le⟩) s (hRs s hs)⟩)
      (fun s hs => hH x hxab σ hσab (u x) (u σ) s (abs_le.mpr (hRu x hx))
        (abs_le.mpr (hRu σ ⟨le_rfl, hστ.le⟩)) (abs_le.mpr (hRs s hs)))
    have hF2 : |Lv x (u x) k - Lv σ (u σ) k| ≤ A' := by
      rw [hA']
      refine hF2'.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
      exact Real.rpow_le_rpow (by positivity) hd (by linarith)
    -- F₃ : Hölder de L en w
    have hux : |u x - (u σ + k * (x - σ))| ≤ 2 * N * Real.sqrt ε := by
      have h1 := abs_sub_le (u x) (u σ) (u σ + k * (x - σ))
      rw [abs_sub_comm (u σ)] at h1
      have h2 := hdiffσ x hx
      have h3 := hcσ x hx
      linarith
    have hF3 : |L x (u x) k - L x (u σ + k * (x - σ)) k| ≤ B' := by
      have h1 := hH x hxab x hxab (u x) (u σ + k * (x - σ)) k (abs_le.mpr (hRu x hx))
        (abs_le.mpr (hRc x hx)) (abs_le.mpr hRk)
      rw [sub_self, abs_zero, zero_add] at h1
      rw [hB']
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
      exact Real.rpow_le_rpow (abs_nonneg _) hux hα.le
    exact pointwise_F hμ hF1 hF2 hF3
  -- étape 3 : intégration
  have h24 := good_interval_ineq hL hu haσ hστ hτb hgood
  rw [hk_def] at h24
  have hii_d : IntervalIntegrable (deriv u) volume σ τ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hστ.le).mpr (hInt1.mono_set hsub)
  have hii_d2 : IntervalIntegrable (fun x => deriv u x ^ 2) volume σ τ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hστ.le).mpr (hInt.mono_set hsub)
  have hζ : IntervalIntegrable (fun x => deriv u x - k) volume σ τ :=
    hii_d.sub intervalIntegrable_const
  have hζ2 : IntervalIntegrable (fun x => (deriv u x - k) ^ 2) volume σ τ := by
    have e : (fun x => (deriv u x - k) ^ 2) = fun x => deriv u x ^ 2 - 2 * k * deriv u x + k ^ 2 := by
      funext x
      ring
    rw [e]
    exact (hii_d2.sub (hii_d.const_mul _)).add intervalIntegrable_const
  have hFu : IntervalIntegrable (fun x => L x (u x) (deriv u x)) volume σ τ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hστ.le).mpr (hE.mono_set hsub)
  have hFc : IntervalIntegrable (fun x => L x (u σ + k * (x - σ)) k) volume σ τ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hστ.le]
    have hmaps : MapsTo (fun x : ℝ => (x, u σ + k * (x - σ), k)) (Icc σ τ)
        (Icc a b ×ˢ (univ : Set (ℝ × ℝ))) := fun x hx => ⟨hsub hx, mem_univ _⟩
    exact hL.comp (by fun_prop) hmaps
  have hζ0 : ∫ x in σ..τ, (deriv u x - k) = 0 := by
    rw [intervalIntegral.integral_sub hii_d intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, ← hrep2 σ hσab τ hτab hστ.le]
    rw [hε_def] at hkrel
    linarith
  have hint := integral_step (Fu := fun x => L x (u x) (deriv u x))
    (Fc := fun x => L x (u σ + k * (x - σ)) k) (ζ := fun x => deriv u x - k)
    (pbar := Lv σ (u σ) k) (A := A') (B := B') hστ.le hμ hFu hFc hζ hζ2 h24 hζ0
    (Eventually.of_forall (fun x hx => hpt x (Ioo_subset_Icc_self hx)))
  rw [← hε_def] at hint
  -- calcul des puissances : A² ≤ (2C+Λ)²(1+N) ε^{α/2} et B ≤ C(1+2N) ε^{α/2}
  have hsqrtα : Real.sqrt ε ^ α = ε ^ (α / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hεpos.le]
    congr 1
    ring
  have hX0 : 0 ≤ (1 + N) * Real.sqrt ε := by positivity
  have hXsq : (((1 + N) * Real.sqrt ε) ^ (α / 2)) ^ 2 = ((1 + N) * Real.sqrt ε) ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]
    congr 1
    push_cast
    ring
  have h1N : (1 + N) ^ α ≤ 1 + N := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 1 + N by linarith) hα1
    rwa [Real.rpow_one] at this
  have h12N : (2 * N) ^ α ≤ 1 + 2 * N := by
    have h1 := Real.rpow_le_rpow (show (0 : ℝ) ≤ 2 * N by linarith)
      (show 2 * N ≤ 1 + 2 * N by linarith) hα.le
    have h2 := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 1 + 2 * N by linarith) hα1
    rw [Real.rpow_one] at h2
    linarith
  have hεα0 : 0 ≤ ε ^ (α / 2) := Real.rpow_nonneg hεpos.le _
  have hXα : ((1 + N) * Real.sqrt ε) ^ α ≤ (1 + N) * ε ^ (α / 2) := by
    rw [Real.mul_rpow (by linarith) (Real.sqrt_nonneg _), hsqrtα]
    exact mul_le_mul_of_nonneg_right h1N hεα0
  have hA2 : A' ^ 2 ≤ (2 * C + Λ) ^ 2 * (1 + N) * ε ^ (α / 2) := by
    rw [hA', mul_pow, hXsq]
    have := mul_le_mul_of_nonneg_left hXα (sq_nonneg (2 * C + Λ))
    linarith
  have hB2 : B' ≤ C * (1 + 2 * N) * ε ^ (α / 2) := by
    rw [hB', Real.mul_rpow (by linarith) (Real.sqrt_nonneg _), hsqrtα]
    have := mul_le_mul_of_nonneg_right h12N hεα0
    have := mul_le_mul_of_nonneg_left this hC.le
    linarith
  have hsum : A' ^ 2 / μ + B' ≤
      ((2 * C + Λ) ^ 2 * (1 + N) / μ + C * (1 + 2 * N)) * ε ^ (α / 2) := by
    have h1 : A' ^ 2 / μ ≤ (2 * C + Λ) ^ 2 * (1 + N) * ε ^ (α / 2) / μ :=
      div_le_div_of_nonneg_right hA2 hμ.le
    have e : (2 * C + Λ) ^ 2 * (1 + N) * ε ^ (α / 2) / μ =
        (2 * C + Λ) ^ 2 * (1 + N) / μ * ε ^ (α / 2) := by ring
    nlinarith
  -- conclusion
  obtain ⟨I, hI⟩ : ∃ I, I = ∫ x in σ..τ, (deriv u x - k) ^ 2 := ⟨_, rfl⟩
  rw [← hI] at hint ⊢
  rw [div_le_iff₀ hεpos]
  have h1 := hint.trans (mul_le_mul_of_nonneg_right hsum hεpos.le)
  have h2 : I * μ ≤ ((2 * C + Λ) ^ 2 * (1 + N) / μ + C * (1 + 2 * N)) *
      ε ^ (α / 2) * ε * 4 := by linarith
  calc I ≤ ((2 * C + Λ) ^ 2 * (1 + N) / μ + C * (1 + 2 * N)) * ε ^ (α / 2) * ε * 4 / μ :=
        (le_div_iff₀ hμ).mpr h2
    _ = 4 / μ * ((2 * C + Λ) ^ 2 * (1 + N) / μ + C * (1 + 2 * N)) * ε ^ (α / 2) * ε := by
        ring

/-! ## § 2.5 : la fonction `Θ` et l'inégalité de Cauchy–Schwarz (CS)

On pose `Θ(K,ε) = sup √(dev(σ,τ))`, le sup portant sur les bons intervalles `[σ,τ] ⊆ [a,b]`
de longueur `≤ ε` (et assez courts pour le lemme 2.6), de pente `|k| ≤ K`, où
`dev(σ,τ) = (1/(τ-σ)) ∫_σ^τ (u' - k)²`. -/

/-- La déviation quadratique moyenne de `u'` par rapport à la pente de la corde. -/
def dev (u : ℝ → ℝ) (σ τ : ℝ) : ℝ :=
  (∫ x in σ..τ, (deriv u x - slope u σ τ) ^ 2) / (τ - σ)

/-- L'ensemble dont `Θ(K,ε)` est le sup (on y ajoute `0`). -/
def ThetaSet (a b N : ℝ) (u f g : ℝ → ℝ) (K ε : ℝ) : Set ℝ :=
  insert 0 {r | ∃ σ τ, a ≤ σ ∧ σ < τ ∧ τ ≤ b ∧ τ - σ ≤ ε ∧ (1 + N) * Real.sqrt (τ - σ) ≤ 1 ∧
    (∀ x ∈ Icc σ τ, f x ≤ chord u σ τ x ∧ chord u σ τ x ≤ g x) ∧ |slope u σ τ| ≤ K ∧
    r = Real.sqrt (dev u σ τ)}

/-- La fonction `Θ(K,ε)`. -/
def Theta (a b N : ℝ) (u f g : ℝ → ℝ) (K ε : ℝ) : ℝ := sSup (ThetaSet a b N u f g K ε)

/-- Ce que fournit le lemme 2.6, pour chaque `K`. -/
def EstHyp (a b N : ℝ) (u f g : ℝ → ℝ) : Prop :=
  ∀ K, ∃ C γ : ℝ, 0 < γ ∧ ∀ σ τ, a ≤ σ → σ < τ → τ ≤ b → (1 + N) * Real.sqrt (τ - σ) ≤ 1 →
    (∀ x ∈ Icc σ τ, f x ≤ chord u σ τ x ∧ chord u σ τ x ≤ g x) → |slope u σ τ| ≤ K →
    dev u σ τ ≤ C * (τ - σ) ^ γ

theorem estHyp_of {L : ℝ → ℝ → ℝ → ℝ} {u f g : ℝ → ℝ} {a b A B : ℝ} (hab : a ≤ b)
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2) (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH1 : HypH1 a b L) (hH2 : HypH2 a b L)
    (hu : IsFiniteEnergySolution a b A B L f g u) {N : ℝ} (hN0 : 0 ≤ N)
    (hN : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |u y - u x| ≤ N * Real.sqrt (y - x)) :
    EstHyp a b N u f g := by
  intro K
  obtain ⟨C, γ, hγ, hC⟩ := basic_estimate hab hL hH1 hH2 hu hN0 hN (le_max_right K 0)
  exact ⟨C, γ, hγ, fun σ τ h1 h2 h3 h4 h5 h6 =>
    hC σ τ h1 h2 h3 h4 h5 (h6.trans (le_max_left _ _))⟩

lemma len_le_one {N ℓ : ℝ} (hN0 : 0 ≤ N) (hℓ : 0 ≤ ℓ) (h : (1 + N) * Real.sqrt ℓ ≤ 1) :
    ℓ ≤ 1 := by
  have h1 := Real.sq_sqrt hℓ
  have h2 := Real.sqrt_nonneg ℓ
  have h3 : Real.sqrt ℓ ≤ 1 := by nlinarith [mul_nonneg hN0 h2]
  nlinarith

section Theta

variable {a b N : ℝ} {u f g : ℝ → ℝ}

lemma ThetaSet.le_bound (hN0 : 0 ≤ N) {K ε C γ : ℝ} (hγ : 0 < γ)
    (hC : ∀ σ τ, a ≤ σ → σ < τ → τ ≤ b → (1 + N) * Real.sqrt (τ - σ) ≤ 1 →
      (∀ x ∈ Icc σ τ, f x ≤ chord u σ τ x ∧ chord u σ τ x ≤ g x) → |slope u σ τ| ≤ K →
      dev u σ τ ≤ C * (τ - σ) ^ γ)
    {r : ℝ} (hr : r ∈ ThetaSet a b N u f g K ε) : r ≤ Real.sqrt |C| := by
  rcases Set.mem_insert_iff.mp hr with rfl | ⟨σ, τ, h1, h2, h3, h4, h5, h6, h7, rfl⟩
  · exact Real.sqrt_nonneg _
  · apply Real.sqrt_le_sqrt
    have hℓ : 0 ≤ τ - σ := by linarith
    have hpow : (τ - σ) ^ γ ≤ 1 := Real.rpow_le_one hℓ (len_le_one hN0 hℓ h5) hγ.le
    have hp0 : 0 ≤ (τ - σ) ^ γ := Real.rpow_nonneg hℓ _
    have hd := hC σ τ h1 h2 h3 h5 h6 h7
    have e1 : C * (τ - σ) ^ γ ≤ |C| * (τ - σ) ^ γ :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hp0
    have e2 : |C| * (τ - σ) ^ γ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    linarith

lemma ThetaSet.le_holder (_hN0 : 0 ≤ N) {K ε C γ : ℝ} (hγ : 0 < γ)
    (hC : ∀ σ τ, a ≤ σ → σ < τ → τ ≤ b → (1 + N) * Real.sqrt (τ - σ) ≤ 1 →
      (∀ x ∈ Icc σ τ, f x ≤ chord u σ τ x ∧ chord u σ τ x ≤ g x) → |slope u σ τ| ≤ K →
      dev u σ τ ≤ C * (τ - σ) ^ γ)
    (hε : 0 < ε) {r : ℝ} (hr : r ∈ ThetaSet a b N u f g K ε) :
    r ≤ Real.sqrt |C| * ε ^ (γ / 2) := by
  have hR0 : 0 ≤ Real.sqrt |C| * ε ^ (γ / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hε.le _)
  rcases Set.mem_insert_iff.mp hr with rfl | ⟨σ, τ, h1, h2, h3, h4, h5, h6, h7, rfl⟩
  · exact hR0
  · have hℓ : 0 ≤ τ - σ := by linarith
    have hp : (τ - σ) ^ γ ≤ ε ^ γ := Real.rpow_le_rpow hℓ h4 hγ.le
    have hp0 : 0 ≤ (τ - σ) ^ γ := Real.rpow_nonneg hℓ _
    have hd := hC σ τ h1 h2 h3 h5 h6 h7
    have hb : dev u σ τ ≤ |C| * ε ^ γ := by
      have e1 : C * (τ - σ) ^ γ ≤ |C| * (τ - σ) ^ γ :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hp0
      have e2 : |C| * (τ - σ) ^ γ ≤ |C| * ε ^ γ := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
      linarith
    have he : (ε ^ (γ / 2)) ^ 2 = ε ^ γ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
      congr 1
      push_cast
      ring
    have hsq : (Real.sqrt |C| * ε ^ (γ / 2)) ^ 2 = |C| * ε ^ γ := by
      rw [mul_pow, Real.sq_sqrt (abs_nonneg C), he]
    calc Real.sqrt (dev u σ τ) ≤ Real.sqrt (|C| * ε ^ γ) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt |C| * ε ^ (γ / 2) := by rw [← hsq, Real.sqrt_sq hR0]

lemma Theta.bdd (hN0 : 0 ≤ N) (hE : EstHyp a b N u f g) (K ε : ℝ) :
    BddAbove (ThetaSet a b N u f g K ε) := by
  obtain ⟨C, γ, hγ, hC⟩ := hE K
  exact ⟨Real.sqrt |C|, fun r hr => ThetaSet.le_bound hN0 hγ hC hr⟩

lemma Theta.nonneg (hN0 : 0 ≤ N) (hE : EstHyp a b N u f g) (K ε : ℝ) :
    0 ≤ Theta a b N u f g K ε :=
  le_csSup (Theta.bdd hN0 hE K ε) (Set.mem_insert 0 _)

lemma Theta.mono (hN0 : 0 ≤ N) (hE : EstHyp a b N u f g) {K K' ε ε' : ℝ}
    (hK : K ≤ K') (hε : ε ≤ ε') :
    Theta a b N u f g K ε ≤ Theta a b N u f g K' ε' := by
  apply csSup_le_csSup (Theta.bdd hN0 hE K' ε') (Set.insert_nonempty 0 _)
  intro r hr
  rcases Set.mem_insert_iff.mp hr with rfl | ⟨σ, τ, h1, h2, h3, h4, h5, h6, h7, rfl⟩
  · exact Set.mem_insert 0 _
  · exact Set.mem_insert_of_mem 0 ⟨σ, τ, h1, h2, h3, h4.trans hε, h5, h6, h7.trans hK, rfl⟩

lemma Theta.holder (hN0 : 0 ≤ N) (hE : EstHyp a b N u f g) (K : ℝ) :
    ∃ C γ : ℝ, 0 < γ ∧ ∀ ε, 0 < ε → Theta a b N u f g K ε ≤ C * ε ^ γ := by
  obtain ⟨C, γ, hγ, hC⟩ := hE K
  refine ⟨Real.sqrt |C|, γ / 2, by linarith, fun ε hε => ?_⟩
  exact csSup_le (Set.insert_nonempty 0 _) (fun r hr => ThetaSet.le_holder hN0 hγ hC hε hr)

lemma Theta.le_of_mem (hN0 : 0 ≤ N) (hE : EstHyp a b N u f g) {σ τ : ℝ}
    (h1 : a ≤ σ) (h2 : σ < τ) (h3 : τ ≤ b) (h5 : (1 + N) * Real.sqrt (τ - σ) ≤ 1)
    (h6 : ∀ x ∈ Icc σ τ, f x ≤ chord u σ τ x ∧ chord u σ τ x ≤ g x) :
    Real.sqrt (dev u σ τ) ≤ Theta a b N u f g |slope u σ τ| (τ - σ) :=
  le_csSup (Theta.bdd hN0 hE _ _)
    (Set.mem_insert_of_mem 0 ⟨σ, τ, h1, h2, h3, le_rfl, h5, h6, le_rfl, rfl⟩)

/-- **(CS)** sur un bon intervalle : `|u(t) - u(s) - k(t-s)| ≤ Θ(|k|, τ-σ) √((τ-σ)(t-s))`. -/
theorem cs_of_good (hN0 : 0 ≤ N) (hE : EstHyp a b N u f g)
    (hInt1 : IntegrableOn (deriv u) (Icc a b))
    (hInt : IntegrableOn (fun x => deriv u x ^ 2) (Icc a b))
    (hrep : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → u y - u x = ∫ t in x..y, deriv u t)
    {σ τ : ℝ} (h1 : a ≤ σ) (h2 : σ < τ) (h3 : τ ≤ b) (h5 : (1 + N) * Real.sqrt (τ - σ) ≤ 1)
    (h6 : ∀ x ∈ Icc σ τ, f x ≤ chord u σ τ x ∧ chord u σ τ x ≤ g x)
    {s t : ℝ} (hσs : σ ≤ s) (hst : s < t) (htτ : t ≤ τ) :
    |u t - u s - slope u σ τ * (t - s)| ≤
      Theta a b N u f g |slope u σ τ| (τ - σ) * Real.sqrt ((τ - σ) * (t - s)) := by
  have hΘ := Theta.le_of_mem hN0 hE h1 h2 h3 h5 h6
  have hdev : dev u σ τ * (τ - σ) = ∫ x in σ..τ, (deriv u x - slope u σ τ) ^ 2 := by
    unfold dev
    exact div_mul_cancel₀ _ (sub_pos.mpr h2).ne'
  obtain ⟨k, hk⟩ : ∃ k, slope u σ τ = k := ⟨_, rfl⟩
  rw [hk] at hΘ hdev ⊢
  have hsσ : s ∈ Icc a b := ⟨by linarith, by linarith⟩
  have htσ : t ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hsubst : Icc s t ⊆ Icc a b := Icc_subset_Icc (by linarith) (by linarith)
  have hsubστ : Icc σ τ ⊆ Icc a b := Icc_subset_Icc h1 h3
  have hd_st : IntervalIntegrable (deriv u) volume s t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hst.le).mpr (hInt1.mono_set hsubst)
  have hd2_st : IntervalIntegrable (fun x => deriv u x ^ 2) volume s t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hst.le).mpr (hInt.mono_set hsubst)
  have hd_στ : IntervalIntegrable (deriv u) volume σ τ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le h2.le).mpr (hInt1.mono_set hsubστ)
  have hd2_στ : IntervalIntegrable (fun x => deriv u x ^ 2) volume σ τ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le h2.le).mpr (hInt.mono_set hsubστ)
  have e : (fun x => (deriv u x - k) ^ 2) = fun x => deriv u x ^ 2 - 2 * k * deriv u x + k ^ 2 := by
    funext x
    ring
  have hζ_st : IntervalIntegrable (fun x => deriv u x - k) volume s t :=
    hd_st.sub intervalIntegrable_const
  have hζ2_st : IntervalIntegrable (fun x => (deriv u x - k) ^ 2) volume s t := by
    rw [e]
    exact (hd2_st.sub (hd_st.const_mul _)).add intervalIntegrable_const
  have hζ2_στ : IntervalIntegrable (fun x => (deriv u x - k) ^ 2) volume σ τ := by
    rw [e]
    exact (hd2_στ.sub (hd_στ.const_mul _)).add intervalIntegrable_const
  -- u(t) - u(s) - k(t-s) = ∫_s^t (u' - k)
  have hX : u t - u s - k * (t - s) = ∫ x in s..t, (deriv u x - k) := by
    rw [intervalIntegral.integral_sub hd_st intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, ← hrep s hsσ t htσ hst.le]
    ring
  have hCS := sq_integral_le hst.le hζ_st hζ2_st
  have hmono : ∫ x in s..t, (deriv u x - k) ^ 2 ≤ ∫ x in σ..τ, (deriv u x - k) ^ 2 :=
    intervalIntegral.integral_mono_interval hσs hst.le htτ
      (Eventually.of_forall (fun x => by show (0 : ℝ) ≤ _; positivity)) hζ2_στ
  have hfin : (u t - u s - k * (t - s)) ^ 2 ≤ ((τ - σ) * (t - s)) * dev u σ τ := by
    rw [hX]
    have hts : 0 ≤ t - s := by linarith
    calc (∫ x in s..t, (deriv u x - k)) ^ 2 ≤ (t - s) * ∫ x in s..t, (deriv u x - k) ^ 2 := hCS
      _ ≤ (t - s) * ∫ x in σ..τ, (deriv u x - k) ^ 2 := mul_le_mul_of_nonneg_left hmono hts
      _ = ((τ - σ) * (t - s)) * dev u σ τ := by rw [← hdev]; ring
  have habs := Real.abs_le_sqrt hfin
  rw [Real.sqrt_mul (mul_nonneg (by linarith) (by linarith))] at habs
  calc |u t - u s - k * (t - s)| ≤ Real.sqrt ((τ - σ) * (t - s)) * Real.sqrt (dev u σ τ) := habs
    _ ≤ Real.sqrt ((τ - σ) * (t - s)) * Theta a b N u f g |k| (τ - σ) :=
        mul_le_mul_of_nonneg_left hΘ (Real.sqrt_nonneg _)
    _ = Theta a b N u f g |k| (τ - σ) * Real.sqrt ((τ - σ) * (t - s)) := mul_comm _ _

/-- Un intervalle de type inférieur, assez court, fournit un `LowerFrame` pour `u`. -/
theorem lowerFrame_of (hN0 : 0 ≤ N) (hE : EstHyp a b N u f g)
    (hInt1 : IntegrableOn (deriv u) (Icc a b))
    (hInt : IntegrableOn (fun x => deriv u x ^ 2) (Icc a b))
    (hrep : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → u y - u x = ∫ t in x..y, deriv u t)
    (hcont : ContinuousOn u (Icc a b)) (hfu : ∀ x ∈ Icc a b, f x ≤ u x)
    {ρ₁ : ℝ} (hρ₁ : (1 + N) * Real.sqrt ρ₁ ≤ 1)
    {c d : ℝ} (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) (hlen : d - c ≤ ρ₁)
    (hT : LowerType u g c d) : LowerFrame u c d (Theta a b N u f g) := by
  refine ⟨hcd, hcont.mono (Icc_subset_Icc hac hdb), fun K ε => Theta.nonneg hN0 hE K ε,
    fun K K' ε ε' hK hε => Theta.mono hN0 hE hK hε, Theta.holder hN0 hE, ?_⟩
  intro σ τ hcσ hστ hτd habove s t hσs hst htτ
  have hlenστ : (1 + N) * Real.sqrt (τ - σ) ≤ 1 := by
    refine le_trans ?_ hρ₁
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by linarith)
  refine cs_of_good hN0 hE hInt1 hInt hrep (by linarith) hστ (by linarith) hlenστ ?_ hσs hst htτ
  intro x hx
  rw [chord_of_mem hx]
  have hxab : x ∈ Icc a b := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hxcd : x ∈ Icc c d := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  refine ⟨(hfu x hxab).trans (habove x hx), ?_⟩
  have hrel : (τ - σ) * slope u σ τ = u τ - u σ := by simpa using sub_smul_slope u σ τ
  rcases le_or_gt 0 (slope u σ τ) with hk | hk
  · have h1 : slope u σ τ * (x - σ) ≤ slope u σ τ * (τ - σ) :=
      mul_le_mul_of_nonneg_left (by linarith [hx.2]) hk
    have h2 := hT τ ⟨by linarith, hτd⟩ x hxcd
    linarith
  · have h1 : slope u σ τ * (x - σ) ≤ 0 := by nlinarith [hx.1]
    have h2 := hT σ ⟨hcσ, by linarith⟩ x hxcd
    linarith

/-- Un intervalle de type supérieur, assez court, fournit un `LowerFrame` pour `-u`. -/
theorem upperFrame_of (hN0 : 0 ≤ N) (hE : EstHyp a b N u f g)
    (hInt1 : IntegrableOn (deriv u) (Icc a b))
    (hInt : IntegrableOn (fun x => deriv u x ^ 2) (Icc a b))
    (hrep : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → u y - u x = ∫ t in x..y, deriv u t)
    (hcont : ContinuousOn u (Icc a b)) (hug : ∀ x ∈ Icc a b, u x ≤ g x)
    {ρ₁ : ℝ} (hρ₁ : (1 + N) * Real.sqrt ρ₁ ≤ 1)
    {c d : ℝ} (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) (hlen : d - c ≤ ρ₁)
    (hT : UpperType u f c d) : LowerFrame (fun y => -u y) c d (Theta a b N u f g) := by
  refine ⟨hcd, hcont.neg.mono (Icc_subset_Icc hac hdb), fun K ε => Theta.nonneg hN0 hE K ε,
    fun K K' ε ε' hK hε => Theta.mono hN0 hE hK hε, Theta.holder hN0 hE, ?_⟩
  intro σ τ hcσ hστ hτd habove s t hσs hst htτ
  have hbelow : ∀ x ∈ Icc σ τ, u σ + slope u σ τ * (x - σ) ≤ u x := by
    intro x hx
    have h := habove x hx
    rw [slope_neg_fun] at h
    have h' : -u x ≤ -u σ + -slope u σ τ * (x - σ) := h
    linarith
  have hlenστ : (1 + N) * Real.sqrt (τ - σ) ≤ 1 := by
    refine le_trans ?_ hρ₁
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by linarith)
  have key : |u t - u s - slope u σ τ * (t - s)| ≤
      Theta a b N u f g |slope u σ τ| (τ - σ) * Real.sqrt ((τ - σ) * (t - s)) := by
    refine cs_of_good hN0 hE hInt1 hInt hrep (by linarith) hστ (by linarith) hlenστ ?_
      hσs hst htτ
    intro x hx
    rw [chord_of_mem hx]
    have hxab : x ∈ Icc a b := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxcd : x ∈ Icc c d := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    refine ⟨?_, (hbelow x hx).trans (hug x hxab)⟩
    have hrel : (τ - σ) * slope u σ τ = u τ - u σ := by simpa using sub_smul_slope u σ τ
    rcases le_or_gt 0 (slope u σ τ) with hk | hk
    · have h1 : 0 ≤ slope u σ τ * (x - σ) := mul_nonneg hk (by linarith [hx.1])
      have h2 := hT σ ⟨hcσ, by linarith⟩ x hxcd
      linarith
    · have h1 : slope u σ τ * (τ - σ) ≤ slope u σ τ * (x - σ) := by nlinarith [hx.2]
      have h2 := hT τ ⟨by linarith, hτd⟩ x hxcd
      linarith
  show |-u t - -u s - slope (fun y => -u y) σ τ * (t - s)| ≤
    Theta a b N u f g |slope (fun y => -u y) σ τ| (τ - σ) * Real.sqrt ((τ - σ) * (t - s))
  rw [slope_neg_fun, abs_neg]
  have e : -u t - -u s - -slope u σ τ * (t - s) = -(u t - u s - slope u σ τ * (t - s)) := by
    ring
  rw [e, abs_neg]
  exact key

end Theta

/-- **Construction du cadre global** de la Section 4 à partir d'une solution d'énergie finie. -/
theorem global_frame {L : ℝ → ℝ → ℝ → ℝ} {u f g : ℝ → ℝ} {a b A B : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x < g x)
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2) (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH1 : HypH1 a b L) (hH2 : HypH2 a b L)
    (hu : IsFiniteEnergySolution a b A B L f g u) :
    ∃ Θ ρ₀, GlobalFrame u f g a b Θ ρ₀ := by
  have hu' := hu
  obtain ⟨⟨hW, -, -, hfgu⟩, hE, -⟩ := hu'
  obtain ⟨hInt, N, hN0, hN⟩ := holder_half hab.le hL hH2 hW hE
  obtain ⟨hInt1, hrep⟩ := W11_deriv_facts hab.le hL hH2 hW hE
  have hcont := W11_continuousOn hab.le hW
  have hEst := estHyp_of hab.le hL hH1 hH2 hu hN0 hN
  have h1N : 0 < 1 + N := by linarith
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁ : ℝ, ρ₁ = (1 / (1 + N)) ^ 2 := ⟨_, rfl⟩
  have hρ₁pos : 0 < ρ₁ := by rw [hρ₁]; positivity
  have hρ₁N : (1 + N) * Real.sqrt ρ₁ ≤ 1 := by
    rw [hρ₁, Real.sqrt_sq (by positivity)]
    exact (mul_one_div_cancel h1N.ne').le
  obtain ⟨ρ₀, hρ₀, hρ₀₁, hdich, hcf, hcg, hfree⟩ := exists_rho0 hab hcont hf hg hfg hρ₁pos
  refine ⟨Theta a b N u f g, ρ₀, ?_⟩
  exact {
    lt := hab
    ρpos := hρ₀
    fu := fun x hx => (hfgu x hx).1
    ug := fun x hx => (hfgu x hx).2
    lower := fun c d hac hcd hdb hlen hT =>
      lowerFrame_of hN0 hEst hInt1 hInt hrep hcont (fun x hx => (hfgu x hx).1) hρ₁N
        hac hcd hdb (hlen.trans hρ₀₁) hT
    upper := fun c d hac hcd hdb hlen hT =>
      upperFrame_of hN0 hEst hInt1 hInt hrep hcont (fun x hx => (hfgu x hx).2) hρ₁N
        hac hcd hdb (hlen.trans hρ₀₁) hT
    dich := hdich
    contact_f := hcf
    contact_g := hcg
    free := hfree }

end TonelliObstacle
