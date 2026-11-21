import Project.Statement
import Project.Section3

/-!
# Section 4 : preuve du résultat principal (cadre abstrait)

On travaille sur `[a,b]` avec une fonction `u` comprise entre deux obstacles `f ≤ u ≤ g`.
La structure `GlobalFrame` rassemble ce que la Section 4 utilise de la Section 2 :
* sur tout intervalle court de type inférieur, `u` vérifie le cadre `LowerFrame` ;
* sur tout intervalle court de type supérieur, `-u` vérifie le cadre `LowerFrame` (symétrie (S₁)) ;
* tout intervalle court est de type inférieur ou supérieur ;
* un intervalle court contenant un point de contact avec `f` (resp. `g`) est de type
  inférieur (resp. supérieur) ;
* un point libre admet un voisinage court qui est des deux types.
-/

open Set Filter Topology

noncomputable section

namespace TonelliObstacle

/-- `J = [c,d]` est de type inférieur : `max_J u < min_J g`. -/
def LowerType (u g : ℝ → ℝ) (c d : ℝ) : Prop :=
  ∀ y ∈ Icc c d, ∀ z ∈ Icc c d, u y < g z

/-- `J = [c,d]` est de type supérieur : `min_J u > max_J f`. -/
def UpperType (u f : ℝ → ℝ) (c d : ℝ) : Prop :=
  ∀ y ∈ Icc c d, ∀ z ∈ Icc c d, f z < u y

/-- Ce que la Section 4 utilise de la Section 2, sur `[a,b]`. -/
structure GlobalFrame (u f g : ℝ → ℝ) (a b : ℝ) (Θ : ℝ → ℝ → ℝ) (ρ₀ : ℝ) : Prop where
  lt : a < b
  ρpos : 0 < ρ₀
  fu : ∀ x ∈ Icc a b, f x ≤ u x
  ug : ∀ x ∈ Icc a b, u x ≤ g x
  lower : ∀ c d, a ≤ c → c < d → d ≤ b → d - c ≤ ρ₀ → LowerType u g c d →
    LowerFrame u c d Θ
  upper : ∀ c d, a ≤ c → c < d → d ≤ b → d - c ≤ ρ₀ → UpperType u f c d →
    LowerFrame (fun y => -u y) c d Θ
  dich : ∀ c d, a ≤ c → c < d → d ≤ b → d - c ≤ ρ₀ →
    LowerType u g c d ∨ UpperType u f c d
  contact_f : ∀ c d x, a ≤ c → c < d → d ≤ b → d - c ≤ ρ₀ → x ∈ Icc c d → u x = f x →
    LowerType u g c d
  contact_g : ∀ c d x, a ≤ c → c < d → d ≤ b → d - c ≤ ρ₀ → x ∈ Icc c d → u x = g x →
    UpperType u f c d
  free : ∀ x ∈ Ioo a b, f x < u x → u x < g x → ∃ c d, a ≤ c ∧ c < x ∧ x < d ∧ d ≤ b ∧
    d - c ≤ ρ₀ ∧ LowerType u g c d ∧ UpperType u f c d

/-! ## Outils : pentes de `-u` et comparaison des pentes au contact -/

/-- La pente de `-u` est l'opposée de celle de `u`. -/
lemma slope_neg_fun (u : ℝ → ℝ) (s t : ℝ) : slope (fun y => -u y) s t = - slope u s t := by
  simp only [slope_def_field]
  ring

/-- Si les pentes à droite de `u` tendent vers `p`, celles de `-u` tendent vers `-p`. -/
lemma tendsto_neg_right {u : ℝ → ℝ} {x : ℝ} {p : EReal}
    (hp : Tendsto (fun ρ => ((slope u x (x + ρ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 p)) :
    Tendsto (fun ρ => ((slope (fun y => -u y) x (x + ρ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (-p)) := by
  simp only [slope_neg_fun, EReal.coe_neg]
  exact (continuous_neg.tendsto p).comp hp

/-- Si les pentes à gauche de `u` tendent vers `q`, celles de `-u` tendent vers `-q`. -/
lemma tendsto_neg_left {u : ℝ → ℝ} {x : ℝ} {q : EReal}
    (hq : Tendsto (fun ρ => ((slope u (x - ρ) x : ℝ) : EReal)) (𝓝[>] 0) (𝓝 q)) :
    Tendsto (fun ρ => ((slope (fun y => -u y) (x - ρ) x : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (-q)) := by
  simp only [slope_neg_fun, EReal.coe_neg]
  exact (continuous_neg.tendsto q).comp hq

/-- Comparaison des pentes à droite de deux fonctions qui coïncident en `x`. -/
lemma slope_right_le {u v : ℝ → ℝ} {x t : ℝ} (ht : 0 < t) (hx : u x = v x)
    (hle : u (x + t) ≤ v (x + t)) : slope u x (x + t) ≤ slope v x (x + t) := by
  have h1 : t * slope u x (x + t) = u (x + t) - u x := by
    simpa using sub_smul_slope u x (x + t)
  have h2 : t * slope v x (x + t) = v (x + t) - v x := by
    simpa using sub_smul_slope v x (x + t)
  exact le_of_mul_le_mul_left (by linarith) ht

/-- Comparaison des pentes à gauche de deux fonctions qui coïncident en `x`. -/
lemma slope_left_le {u v : ℝ → ℝ} {x t : ℝ} (ht : 0 < t) (hx : u x = v x)
    (hle : v (x - t) ≤ u (x - t)) : slope u (x - t) x ≤ slope v (x - t) x := by
  have h1 : t * slope u (x - t) x = u x - u (x - t) := by
    simpa using sub_smul_slope u (x - t) x
  have h2 : t * slope v (x - t) x = v x - v (x - t) := by
    simpa using sub_smul_slope v (x - t) x
  exact le_of_mul_le_mul_left (by linarith) ht

variable {u f g : ℝ → ℝ} {a b : ℝ} {Θ : ℝ → ℝ → ℝ} {ρ₀ : ℝ}

/-! ## Existence des dérivées unilatérales (aucune condition sur les obstacles) -/

/-- `u'₊(x)` existe dans `[-∞,∞]` pour tout `x ∈ [a, b[`. -/
lemma GlobalFrame.exists_right (hG : GlobalFrame u f g a b Θ ρ₀) {x : ℝ} (hx : x ∈ Ico a b) :
    ∃ p : EReal, Tendsto (fun ρ => ((slope u x (x + ρ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 p) := by
  obtain ⟨r, hr⟩ : ∃ r, r = min ρ₀ (b - x) := ⟨_, rfl⟩
  have hrpos : 0 < r := by rw [hr]; exact lt_min hG.ρpos (by linarith [hx.2])
  have hr1 : r ≤ ρ₀ := by rw [hr]; exact min_le_left _ _
  have hr2 : r ≤ b - x := by rw [hr]; exact min_le_right _ _
  rcases hG.dich x (x + r) hx.1 (by linarith) (by linarith) (by linarith) with hL | hU
  · exact (hG.lower x (x + r) hx.1 (by linarith) (by linarith) (by linarith) hL).exists_right_deriv
      ⟨le_rfl, by linarith⟩
  · obtain ⟨p, hp⟩ := (hG.upper x (x + r) hx.1 (by linarith) (by linarith) (by linarith)
      hU).exists_right_deriv ⟨le_rfl, by linarith⟩
    refine ⟨-p, ?_⟩
    have := tendsto_neg_right hp
    simpa using this

/-- `u'₋(x)` existe dans `[-∞,∞]` pour tout `x ∈ ]a, b]`. -/
lemma GlobalFrame.exists_left (hG : GlobalFrame u f g a b Θ ρ₀) {x : ℝ} (hx : x ∈ Ioc a b) :
    ∃ q : EReal, Tendsto (fun ρ => ((slope u (x - ρ) x : ℝ) : EReal)) (𝓝[>] 0) (𝓝 q) := by
  obtain ⟨r, hr⟩ : ∃ r, r = min ρ₀ (x - a) := ⟨_, rfl⟩
  have hrpos : 0 < r := by rw [hr]; exact lt_min hG.ρpos (by linarith [hx.1])
  have hr1 : r ≤ ρ₀ := by rw [hr]; exact min_le_left _ _
  have hr2 : r ≤ x - a := by rw [hr]; exact min_le_right _ _
  rcases hG.dich (x - r) x (by linarith) (by linarith) hx.2 (by linarith) with hL | hU
  · exact (hG.lower (x - r) x (by linarith) (by linarith) hx.2 (by linarith) hL).exists_left_deriv
      ⟨by linarith, le_rfl⟩
  · obtain ⟨q, hq⟩ := (hG.upper (x - r) x (by linarith) (by linarith) hx.2 (by linarith)
      hU).exists_left_deriv ⟨by linarith, le_rfl⟩
    refine ⟨-q, ?_⟩
    have := tendsto_neg_left hq
    simpa using this

/-! ## Lemme 4.1 : existence de la dérivée et assertion (i) -/

/-- **Lemme 4.1** (aux points intérieurs) : sous (O_f) et (O_g), les dérivées unilatérales
de `u` coïncident, et au contact elles sont données par les dérivés de Dini de l'obstacle. -/
theorem GlobalFrame.one_sided_eq (hG : GlobalFrame u f g a b Θ ρ₀)
    (hOf : ∀ x ∈ Ioo a b, u x = f x → dLowerLeft f x ≤ dUpperRight f x)
    (hOg : ∀ x ∈ Ioo a b, u x = g x → dLowerRight g x ≤ dUpperLeft g x)
    {x : ℝ} (hx : x ∈ Ioo a b) {p q : EReal}
    (hp : Tendsto (fun ρ => ((slope u x (x + ρ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 p))
    (hq : Tendsto (fun ρ => ((slope u (x - ρ) x : ℝ) : EReal)) (𝓝[>] 0) (𝓝 q)) :
    p = q ∧ (u x = f x → p = dLowerLeft f x ∧ p = dUpperRight f x) ∧
      (u x = g x → p = dLowerRight g x ∧ p = dUpperLeft g x) := by
  have hxab : x ∈ Icc a b := ⟨hx.1.le, hx.2.le⟩
  -- un intervalle court [x - r, x + r] autour de x
  obtain ⟨r, hr⟩ : ∃ r, r = min (ρ₀ / 2) (min (x - a) (b - x)) := ⟨_, rfl⟩
  have hrpos : 0 < r := by
    rw [hr]
    exact lt_min (by linarith [hG.ρpos]) (lt_min (by linarith [hx.1]) (by linarith [hx.2]))
  have hr1 : r ≤ ρ₀ / 2 := by rw [hr]; exact min_le_left _ _
  have hr2 : r ≤ x - a := by rw [hr]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ b - x := by rw [hr]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hJ1 : a ≤ x - r := by linarith
  have hJ2 : x - r < x + r := by linarith
  have hJ3 : x + r ≤ b := by linarith
  have hJ4 : x + r - (x - r) ≤ ρ₀ := by linarith
  have hxJ : x ∈ Ioo (x - r) (x + r) := ⟨by linarith, by linarith⟩
  have hxJ' : x ∈ Icc (x - r) (x + r) := ⟨by linarith, by linarith⟩
  -- pas de coin convexe (type inférieur) / pas de coin concave (type supérieur)
  have hlowcorner : LowerType u g (x - r) (x + r) → p ≤ q := fun hL =>
    (hG.lower _ _ hJ1 hJ2 hJ3 hJ4 hL).no_convex_corner hxJ hp hq
  have hupcorner : UpperType u f (x - r) (x + r) → q ≤ p := fun hU =>
    EReal.neg_le_neg_iff.mp ((hG.upper _ _ hJ1 hJ2 hJ3 hJ4 hU).no_convex_corner hxJ
      (tendsto_neg_right hp) (tendsto_neg_left hq))
  -- t petit : x ± t ∈ [a, b]
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < r :=
    hpos.and (nhdsWithin_le_nhds (eventually_lt_nhds hrpos))
  -- au contact avec f : q ≤ D₋f(x) et D⁺f(x) ≤ p
  have hcf : u x = f x → q ≤ dLowerLeft f x ∧ dUpperRight f x ≤ p := by
    intro h1
    have hR : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope f x (x + t) ≤ slope u x (x + t) := by
      filter_upwards [hev] with t ht
      exact slope_right_le ht.1 h1.symm (hG.fu _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hL : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope u (x - t) x ≤ slope f (x - t) x := by
      filter_upwards [hev] with t ht
      exact slope_left_le ht.1 h1 (hG.fu _ ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    constructor
    · rw [← hq.liminf_eq]
      unfold dLowerLeft
      exact liminf_le_liminf (by
        filter_upwards [hL] with t ht
        exact EReal.coe_le_coe_iff.mpr ht)
    · rw [← hp.limsup_eq]
      unfold dUpperRight
      exact limsup_le_limsup (by
        filter_upwards [hR] with t ht
        exact EReal.coe_le_coe_iff.mpr ht)
  -- au contact avec g : p ≤ D₊g(x) et D⁻g(x) ≤ q
  have hcg : u x = g x → p ≤ dLowerRight g x ∧ dUpperLeft g x ≤ q := by
    intro h2
    have hR : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope u x (x + t) ≤ slope g x (x + t) := by
      filter_upwards [hev] with t ht
      exact slope_right_le ht.1 h2 (hG.ug _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hL : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope g (x - t) x ≤ slope u (x - t) x := by
      filter_upwards [hev] with t ht
      exact slope_left_le ht.1 h2.symm (hG.ug _ ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    constructor
    · rw [← hp.liminf_eq]
      unfold dLowerRight
      exact liminf_le_liminf (by
        filter_upwards [hR] with t ht
        exact EReal.coe_le_coe_iff.mpr ht)
    · rw [← hq.limsup_eq]
      unfold dUpperLeft
      exact limsup_le_limsup (by
        filter_upwards [hL] with t ht
        exact EReal.coe_le_coe_iff.mpr ht)
  -- p = q dans les trois cas : contact avec f, contact avec g, point libre
  have peq : p = q := by
    by_cases h1 : u x = f x
    · have hpq := hlowcorner (hG.contact_f _ _ x hJ1 hJ2 hJ3 hJ4 hxJ' h1)
      obtain ⟨A, B⟩ := hcf h1
      exact le_antisymm hpq (A.trans ((hOf x hx h1).trans B))
    · by_cases h2 : u x = g x
      · have hqp := hupcorner (hG.contact_g _ _ x hJ1 hJ2 hJ3 hJ4 hxJ' h2)
        obtain ⟨A, B⟩ := hcg h2
        exact le_antisymm (A.trans ((hOg x hx h2).trans B)) hqp
      · have hfu : f x < u x := lt_of_le_of_ne (hG.fu x hxab) (fun h => h1 h.symm)
        have hug : u x < g x := lt_of_le_of_ne (hG.ug x hxab) h2
        obtain ⟨c', d', hc, hcx, hxd, hd, hlen, hL, hU⟩ := hG.free x hx hfu hug
        have hxJ2 : x ∈ Ioo c' d' := ⟨hcx, hxd⟩
        exact le_antisymm
          ((hG.lower c' d' hc (hcx.trans hxd) hd hlen hL).no_convex_corner hxJ2 hp hq)
          (EReal.neg_le_neg_iff.mp
            ((hG.upper c' d' hc (hcx.trans hxd) hd hlen hU).no_convex_corner hxJ2
              (tendsto_neg_right hp) (tendsto_neg_left hq)))
  refine ⟨peq, fun h1 => ?_, fun h2 => ?_⟩
  · -- q ≤ D₋f ≤ D⁺f ≤ p = q
    obtain ⟨A, B⟩ := hcf h1
    have C := hOf x hx h1
    refine ⟨le_antisymm (by rw [peq]; exact A) (C.trans B),
      le_antisymm (by rw [peq]; exact A.trans C) B⟩
  · -- p ≤ D₊g ≤ D⁻g ≤ q = p
    obtain ⟨A, B⟩ := hcg h2
    have C := hOg x hx h2
    refine ⟨le_antisymm A (C.trans (B.trans peq.symm.le)),
      le_antisymm (A.trans C) (B.trans peq.symm.le)⟩

/-! ## Lemme 4.2 : dérivabilité stricte, cas d'une dérivée finie (cadre `LowerFrame`) -/

section StrictReal

variable {c d : ℝ}

/-- Monotonie de `E` en ses deux variables. -/
lemma LowerFrame.E_mono (hF : LowerFrame u c d Θ) {K K' r r' : ℝ} (hK : K ≤ K') (hr : 0 < r)
    (hrr : r ≤ r') : E Θ K r ≤ E Θ K' r' := by
  unfold E
  have h1 := hF.summable_theta K r hr
  have h2 := hF.summable_theta K' r' (hr.trans_le hrr)
  have : ∑' j : ℕ, Θ K (r / 2 ^ j) ≤ ∑' j : ℕ, Θ K' (r' / 2 ^ j) :=
    Summable.tsum_le_tsum (fun j => hF.mono _ _ _ _ hK (by gcongr)) h1 h2
  linarith

/-- Pentes et symétrie `y ↦ c + d - y` : `k_ũ(c+d-t, c+d-s) = -k_u(s,t)`. -/
lemma slope_reflect_gen (u : ℝ → ℝ) (c d s t : ℝ) :
    slope (fun y => u (c + d - y)) (c + d - t) (c + d - s) = - slope u s t := by
  simp only [slope_def_field]
  have e1 : c + d - (c + d - s) = s := by ring
  have e2 : c + d - (c + d - t) = t := by ring
  have e3 : c + d - s - (c + d - t) = t - s := by ring
  rw [e1, e2, e3]
  ring

/-- **Lemme 4.2, étape 2, côté droit** : si `u'₊(x₀) = p` est fini, alors
`p - 4η ≤ k(s,t) ≤ p + 4η` pour `x₀ ≤ s < t ≤ x₀ + r`. -/
lemma LowerFrame.strict_right (hF : LowerFrame u c d Θ) {x₀ p η : ℝ} (hx₀ : x₀ ∈ Ico c d)
    (hR : Tendsto (fun ρ => slope u x₀ (x₀ + ρ)) (𝓝[>] 0) (𝓝 p)) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ r > 0, ∀ s t, x₀ ≤ s → s < t → t ≤ x₀ + r →
      p - 4 * η ≤ slope u s t ∧ slope u s t ≤ p + 4 * η := by
  obtain ⟨M, hM⟩ : ∃ M, M = |p| + 4 := ⟨_, rfl⟩
  -- E(M, ·) < η et |k(x₀, x₀ + h) - p| < η pour les petites échelles
  obtain ⟨r1, hr1, H1⟩ := exists_pos_of_eventually
    ((hF.E_tendsto_zero M).eventually_lt_const hη)
  obtain ⟨r2, hr2, H2⟩ := exists_pos_of_eventually
    (hR.eventually (Ioo_mem_nhds (show p - η < p by linarith) (show p < p + η by linarith)))
  obtain ⟨r, hr⟩ : ∃ r, r = min (min (r1 / 4) (r2 / 4)) ((d - x₀) / 2) := ⟨_, rfl⟩
  have hrpos : 0 < r := by
    rw [hr]
    exact lt_min (lt_min (by linarith) (by linarith)) (by linarith [hx₀.2])
  have hra : r ≤ r1 / 4 := by rw [hr]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hrb : r ≤ r2 / 4 := by rw [hr]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hrc : r ≤ (d - x₀) / 2 := by rw [hr]; exact min_le_right _ _
  have hE2r : E Θ M (2 * r) < η := H1 (2 * r) (by linarith) (by linarith)
  have hk : ∀ h, 0 < h → h ≤ 2 * r →
      p - η < slope u x₀ (x₀ + h) ∧ slope u x₀ (x₀ + h) < p + η :=
    fun h hh hh2 => H2 h hh (by linarith)
  refine ⟨r, hrpos, fun s t hs hst ht => ?_⟩
  have hsr : s - x₀ ≤ r := by linarith
  -- minoration : k(s, s + r) ≥ p - 3η
  have hlow1 : p - 3 * η ≤ slope u s (s + r) := by
    rcases eq_or_lt_of_le hs with h0 | h0
    · rw [← h0]
      have := hk r hrpos (by linarith)
      linarith [this.1]
    · have A := hk (s - x₀) (by linarith) (by linarith)
      have B := hk (s + r - x₀) (by linarith) (by linarith)
      rw [show x₀ + (s - x₀) = s by ring] at A
      rw [show x₀ + (s + r - x₀) = s + r by ring] at B
      have hA : (s - x₀) * slope u x₀ s = u s - u x₀ := by
        simpa using sub_smul_slope u x₀ s
      have hB : (s + r - x₀) * slope u x₀ (s + r) = u (s + r) - u x₀ := by
        simpa using sub_smul_slope u x₀ (s + r)
      have hC : r * slope u s (s + r) = u (s + r) - u s := by
        simpa using sub_smul_slope u s (s + r)
      have P1 := mul_le_mul_of_nonneg_left B.1.le (show 0 ≤ s + r - x₀ by linarith)
      have P2 := mul_le_mul_of_nonneg_left A.2.le (show 0 ≤ s - x₀ by linarith)
      have P3 := mul_le_mul_of_nonneg_left hsr hη.le
      have : r * (p - 3 * η) ≤ r * slope u s (s + r) := by linarith
      exact le_of_mul_le_mul_left this hrpos
  have habs1 : |p - 3 * η| ≤ |p| + 3 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le p, le_abs_self p]
  have hEle : E Θ (|p - 3 * η| + 1) r ≤ E Θ M (2 * r) :=
    hF.E_mono (by linarith) hrpos (by linarith)
  have key := hF.slope_mono_right hrpos (by linarith [hx₀.1]) (by linarith) (by linarith) hlow1
    (t - s) ⟨by linarith, by linarith⟩
  rw [show s + (t - s) = t by ring] at key
  refine ⟨by linarith, ?_⟩
  -- majoration
  rcases eq_or_lt_of_le hs with h0 | h0
  · rw [← h0]
    have := hk (t - x₀) (by linarith) (by linarith)
    rw [show x₀ + (t - x₀) = t by ring] at this
    linarith [this.2]
  · have hkt := hk (t - x₀) (by linarith) (by linarith)
    rw [show x₀ + (t - x₀) = t by ring] at hkt
    have habs2 : |p + η| ≤ |p| + 1 := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le p, le_abs_self p]
    have hEle2 : E Θ (|p + η| + 1) (t - x₀) ≤ E Θ M (2 * r) :=
      hF.E_mono (by linarith) (by linarith) (by linarith)
    have key2 := hF.slope_mono_left (x := t) (ℓ := p + η) (r := t - x₀) (by linarith)
      (by rw [show t - (t - x₀) = x₀ by ring]; exact hx₀.1) (by linarith) (by linarith)
      (by rw [show t - (t - x₀) = x₀ by ring]; exact hkt.2.le) (t - s)
      ⟨by linarith, by linarith⟩
    rw [show t - (t - s) = s by ring] at key2
    linarith

/-- **Lemme 4.2, étape 2, côté gauche**, par la symétrie (S₂). -/
lemma LowerFrame.strict_left (hF : LowerFrame u c d Θ) {x₀ p η : ℝ} (hx₀ : x₀ ∈ Ioc c d)
    (hL : Tendsto (fun ρ => slope u (x₀ - ρ) x₀) (𝓝[>] 0) (𝓝 p)) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ r > 0, ∀ s t, s < t → t ≤ x₀ → x₀ - r ≤ s →
      p - 4 * η ≤ slope u s t ∧ slope u s t ≤ p + 4 * η := by
  have hR' : Tendsto (fun ρ => slope (fun y => u (c + d - y)) (c + d - x₀) (c + d - x₀ + ρ))
      (𝓝[>] 0) (𝓝 (-p)) := by
    simp only [slope_reflect u c d x₀]
    exact hL.neg
  obtain ⟨r, hr, H⟩ := hF.reflect.strict_right ⟨by linarith [hx₀.2], by linarith [hx₀.1]⟩
    hR' hη hη1
  refine ⟨r, hr, fun s t hst htx hsx => ?_⟩
  have := H (c + d - t) (c + d - s) (by linarith) (by linarith) (by linarith)
  rw [slope_reflect_gen] at this
  constructor <;> linarith [this.1, this.2]

/-- **Lemme 4.2, cas `p` fini** : `p - 4η ≤ k(s,t) ≤ p + 4η` pour `s < t` dans
`[x₀ - r, x₀ + r] ∩ [c, d]`. -/
lemma LowerFrame.strict_real (hF : LowerFrame u c d Θ) {x₀ p η : ℝ} (hx₀ : x₀ ∈ Icc c d)
    (hR : x₀ < d → Tendsto (fun ρ => slope u x₀ (x₀ + ρ)) (𝓝[>] 0) (𝓝 p))
    (hL : c < x₀ → Tendsto (fun ρ => slope u (x₀ - ρ) x₀) (𝓝[>] 0) (𝓝 p))
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ r > 0, ∀ s t, c ≤ s → s < t → t ≤ d → x₀ - r ≤ s → t ≤ x₀ + r →
      p - 4 * η ≤ slope u s t ∧ slope u s t ≤ p + 4 * η := by
  -- côté droit
  have hRpart : ∃ r > 0, ∀ s t, x₀ ≤ s → s < t → t ≤ d → t ≤ x₀ + r →
      p - 4 * η ≤ slope u s t ∧ slope u s t ≤ p + 4 * η := by
    by_cases hd : x₀ < d
    · obtain ⟨r, hr, H⟩ := hF.strict_right ⟨hx₀.1, hd⟩ (hR hd) hη hη1
      exact ⟨r, hr, fun s t h1 h2 _ h4 => H s t h1 h2 h4⟩
    · refine ⟨1, one_pos, fun s t h1 h2 h3 _ => ?_⟩
      exfalso
      linarith [hx₀.2]
  -- côté gauche
  have hLpart : ∃ r > 0, ∀ s t, c ≤ s → s < t → t ≤ x₀ → x₀ - r ≤ s →
      p - 4 * η ≤ slope u s t ∧ slope u s t ≤ p + 4 * η := by
    by_cases hc : c < x₀
    · obtain ⟨r, hr, H⟩ := hF.strict_left ⟨hc, hx₀.2⟩ (hL hc) hη hη1
      exact ⟨r, hr, fun s t _ h2 h3 h4 => H s t h2 h3 h4⟩
    · refine ⟨1, one_pos, fun s t h1 h2 h3 _ => ?_⟩
      exfalso
      linarith [hx₀.1]
  obtain ⟨rR, hrR, HR⟩ := hRpart
  obtain ⟨rL, hrL, HL⟩ := hLpart
  refine ⟨min rR rL, lt_min hrR hrL, fun s t hcs hst htd hsx htx => ?_⟩
  have hm1 := min_le_left rR rL
  have hm2 := min_le_right rR rL
  rcases le_or_gt t x₀ with htx0 | htx0
  · exact HL s t hcs hst htx0 (by linarith)
  rcases le_or_gt x₀ s with hsx0 | hsx0
  · exact HR s t hsx0 hst htd (by linarith)
  -- cas s < x₀ < t : k(s,t) est une moyenne pondérée de k(s,x₀) et k(x₀,t)
  have A := HL s x₀ hcs hsx0 le_rfl (by linarith)
  have B := HR x₀ t le_rfl htx0 htd (by linarith)
  have h1 : (t - s) * slope u s t = u t - u s := by simpa using sub_smul_slope u s t
  have h2 : (x₀ - s) * slope u s x₀ = u x₀ - u s := by simpa using sub_smul_slope u s x₀
  have h3 : (t - x₀) * slope u x₀ t = u t - u x₀ := by simpa using sub_smul_slope u x₀ t
  have P1 := mul_le_mul_of_nonneg_left A.1 (show 0 ≤ x₀ - s by linarith)
  have P2 := mul_le_mul_of_nonneg_left A.2 (show 0 ≤ x₀ - s by linarith)
  have P3 := mul_le_mul_of_nonneg_left B.1 (show 0 ≤ t - x₀ by linarith)
  have P4 := mul_le_mul_of_nonneg_left B.2 (show 0 ≤ t - x₀ by linarith)
  constructor
  · have : (t - s) * (p - 4 * η) ≤ (t - s) * slope u s t := by linarith
    exact le_of_mul_le_mul_left this (by linarith)
  · have : (t - s) * slope u s t ≤ (t - s) * (p + 4 * η) := by linarith
    exact le_of_mul_le_mul_left this (by linarith)

end StrictReal

/-! ## Lemme 4.2 : dérivabilité stricte, cas `p = +∞` (cadre `LowerFrame`) -/

section StrictTop

variable {c d : ℝ}

/-- **Lemme 4.2, étape 3, côté droit** : si `u'₊(x₀) = +∞`, alors `k(s,t) ≥ ℓ - 1`
pour `x₀ ≤ s < t ≤ x₀ + r`. -/
lemma LowerFrame.strict_top_right (hF : LowerFrame u c d Θ) {x₀ ℓ : ℝ} (hx₀ : x₀ ∈ Ico c d)
    (hR : Tendsto (fun ρ => ((slope u x₀ (x₀ + ρ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤))
    (hℓ : 0 < ℓ) :
    ∃ r > 0, ∀ s t, x₀ ≤ s → s < t → t ≤ x₀ + r → ℓ - 1 ≤ slope u s t := by
  obtain ⟨r1', hr1', H1⟩ := exists_pos_of_eventually
    ((hF.E_tendsto_zero (ℓ + 1)).eventually_lt_const one_pos)
  obtain ⟨r2', hr2', H2⟩ := exists_pos_of_eventually
    (hR.eventually_const_lt (EReal.coe_lt_top (ℓ + 1)))
  obtain ⟨r1, hr1⟩ : ∃ r1, r1 = min (min (r1' / 2) (r2' / 2)) (d - x₀) := ⟨_, rfl⟩
  have hr1pos : 0 < r1 := by
    rw [hr1]
    exact lt_min (lt_min (by linarith) (by linarith)) (by linarith [hx₀.2])
  have hra : r1 ≤ r1' / 2 := by rw [hr1]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hrb : r1 ≤ r2' / 2 := by rw [hr1]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hrc : r1 ≤ d - x₀ := by rw [hr1]; exact min_le_right _ _
  -- k(x₀, x₀ + r1) > ℓ + 1
  have hz : ℓ + 1 < slope u x₀ (x₀ + r1) :=
    EReal.coe_lt_coe_iff.mp (H2 r1 hr1pos (by linarith))
  -- continuité de s ↦ k(s, x₀ + r1) sur [x₀, x₀ + r1/2]
  have hcont : ContinuousOn (fun s => slope u s (x₀ + r1)) (Icc x₀ (x₀ + r1 / 2)) := by
    have hu : ContinuousOn u (Icc x₀ (x₀ + r1 / 2)) :=
      hF.cont.mono (Icc_subset_Icc hx₀.1 (by linarith))
    have heq : (fun s => slope u s (x₀ + r1)) = fun s => (u (x₀ + r1) - u s) / (x₀ + r1 - s) := by
      funext s
      rw [slope_def_field]
    rw [heq]
    exact (continuousOn_const.sub hu).div (continuousOn_const.sub continuousOn_id)
      (fun s hs => (show (0 : ℝ) < x₀ + r1 - s by linarith [hs.2]).ne')
  -- donc k(s, x₀ + r1) > ℓ pour s proche de x₀
  have hcw := hcont.continuousWithinAt (left_mem_Icc.mpr (by linarith))
  have hev : ∀ᶠ s in 𝓝[Icc x₀ (x₀ + r1 / 2)] x₀, ℓ < slope u s (x₀ + r1) :=
    Filter.Tendsto.eventually hcw (lt_mem_nhds (show ℓ < slope u x₀ (x₀ + r1) by linarith))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, Hδ⟩ := hev
  obtain ⟨r, hr⟩ : ∃ r, r = min (δ / 2) (r1 / 2) := ⟨_, rfl⟩
  have hrpos : 0 < r := by rw [hr]; exact lt_min (by linarith) (by linarith)
  have hrδ : r ≤ δ / 2 := by rw [hr]; exact min_le_left _ _
  have hrr1 : r ≤ r1 / 2 := by rw [hr]; exact min_le_right _ _
  refine ⟨r, hrpos, fun s t hs hst ht => ?_⟩
  have hks : ℓ ≤ slope u s (x₀ + r1) := by
    have hdist : dist s x₀ < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith
    exact (Hδ hdist ⟨hs, by linarith⟩).le
  -- Lemme 3.2 (a) en s, à l'échelle x₀ + r1 - s
  have hEle : E Θ (|ℓ| + 1) (x₀ + r1 - s) ≤ E Θ (ℓ + 1) r1 :=
    hF.E_mono (le_of_eq (by rw [abs_of_pos hℓ])) (by linarith) (by linarith)
  have hE1 : E Θ (ℓ + 1) r1 < 1 := H1 r1 hr1pos (by linarith)
  have key := hF.slope_mono_right (x := s) (ℓ := ℓ) (r := x₀ + r1 - s) (by linarith)
    (by linarith [hx₀.1]) (by linarith) (by linarith)
    (by rw [show s + (x₀ + r1 - s) = x₀ + r1 by ring]; exact hks) (t - s)
    ⟨by linarith, by linarith⟩
  rw [show s + (t - s) = t by ring] at key
  linarith

/-- **Lemme 4.2, étape 3, côté gauche** : si `u'₋(x₀) = +∞`, alors `k(s,t) ≥ ℓ - 1`
pour `x₀ - r ≤ s < t ≤ x₀`. -/
lemma LowerFrame.strict_top_left (hF : LowerFrame u c d Θ) {x₀ ℓ : ℝ} (hx₀ : x₀ ∈ Ioc c d)
    (hL : Tendsto (fun ρ => ((slope u (x₀ - ρ) x₀ : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤))
    (hℓ : 0 < ℓ) :
    ∃ r > 0, ∀ s t, s < t → t ≤ x₀ → x₀ - r ≤ s → ℓ - 1 ≤ slope u s t := by
  obtain ⟨r1', hr1', H1⟩ := exists_pos_of_eventually
    ((hF.E_tendsto_zero (ℓ + 1)).eventually_lt_const one_pos)
  obtain ⟨r2', hr2', H2⟩ := exists_pos_of_eventually
    (hL.eventually_const_lt (EReal.coe_lt_top (ℓ + 1)))
  obtain ⟨r, hr⟩ : ∃ r, r = min (min (r1' / 2) (r2' / 2)) (x₀ - c) := ⟨_, rfl⟩
  have hrpos : 0 < r := by
    rw [hr]
    exact lt_min (lt_min (by linarith) (by linarith)) (by linarith [hx₀.1])
  have hra : r ≤ r1' / 2 := by rw [hr]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hrb : r ≤ r2' / 2 := by rw [hr]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hrc : r ≤ x₀ - c := by rw [hr]; exact min_le_right _ _
  refine ⟨r, hrpos, fun s t hst htx hsx => ?_⟩
  have hρ : 0 < x₀ - s := by linarith
  have hks : ℓ + 1 < slope u s x₀ := by
    have := EReal.coe_lt_coe_iff.mp (H2 (x₀ - s) hρ (by linarith))
    rwa [show x₀ - (x₀ - s) = s by ring] at this
  have hE : E Θ (|ℓ| + 1) (x₀ - s) < 1 := by
    rw [abs_of_pos hℓ]
    exact H1 (x₀ - s) hρ (by linarith)
  have key := hF.slope_mono_right (x := s) (ℓ := ℓ) (r := x₀ - s) hρ (by linarith)
    (by linarith [hx₀.2]) hE.le (by rw [show s + (x₀ - s) = x₀ by ring]; linarith)
    (t - s) ⟨by linarith, by linarith⟩
  rw [show s + (t - s) = t by ring] at key
  linarith

/-- **Lemme 4.2, cas `p = +∞`** : `k(s,t) ≥ ℓ - 1` pour `s < t` dans
`[x₀ - r, x₀ + r] ∩ [c, d]`. -/
lemma LowerFrame.strict_top (hF : LowerFrame u c d Θ) {x₀ ℓ : ℝ} (hx₀ : x₀ ∈ Icc c d)
    (hR : x₀ < d → Tendsto (fun ρ => ((slope u x₀ (x₀ + ρ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤))
    (hL : c < x₀ → Tendsto (fun ρ => ((slope u (x₀ - ρ) x₀ : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤))
    (hℓ : 0 < ℓ) :
    ∃ r > 0, ∀ s t, c ≤ s → s < t → t ≤ d → x₀ - r ≤ s → t ≤ x₀ + r →
      ℓ - 1 ≤ slope u s t := by
  have hRpart : ∃ r > 0, ∀ s t, x₀ ≤ s → s < t → t ≤ d → t ≤ x₀ + r →
      ℓ - 1 ≤ slope u s t := by
    by_cases hd : x₀ < d
    · obtain ⟨r, hr, H⟩ := hF.strict_top_right ⟨hx₀.1, hd⟩ (hR hd) hℓ
      exact ⟨r, hr, fun s t h1 h2 _ h4 => H s t h1 h2 h4⟩
    · refine ⟨1, one_pos, fun s t h1 h2 h3 _ => ?_⟩
      exfalso
      linarith [hx₀.2]
  have hLpart : ∃ r > 0, ∀ s t, c ≤ s → s < t → t ≤ x₀ → x₀ - r ≤ s →
      ℓ - 1 ≤ slope u s t := by
    by_cases hc : c < x₀
    · obtain ⟨r, hr, H⟩ := hF.strict_top_left ⟨hc, hx₀.2⟩ (hL hc) hℓ
      exact ⟨r, hr, fun s t _ h2 h3 h4 => H s t h2 h3 h4⟩
    · refine ⟨1, one_pos, fun s t h1 h2 h3 _ => ?_⟩
      exfalso
      linarith [hx₀.1]
  obtain ⟨rR, hrR, HR⟩ := hRpart
  obtain ⟨rL, hrL, HL⟩ := hLpart
  refine ⟨min rR rL, lt_min hrR hrL, fun s t hcs hst htd hsx htx => ?_⟩
  have hm1 := min_le_left rR rL
  have hm2 := min_le_right rR rL
  rcases le_or_gt t x₀ with htx0 | htx0
  · exact HL s t hcs hst htx0 (by linarith)
  rcases le_or_gt x₀ s with hsx0 | hsx0
  · exact HR s t hsx0 hst htd (by linarith)
  -- cas s < x₀ < t : moyenne pondérée
  have A := HL s x₀ hcs hsx0 le_rfl (by linarith)
  have B := HR x₀ t le_rfl htx0 htd (by linarith)
  have h1 : (t - s) * slope u s t = u t - u s := by simpa using sub_smul_slope u s t
  have h2 : (x₀ - s) * slope u s x₀ = u x₀ - u s := by simpa using sub_smul_slope u s x₀
  have h3 : (t - x₀) * slope u x₀ t = u t - u x₀ := by simpa using sub_smul_slope u x₀ t
  have P1 := mul_le_mul_of_nonneg_left A (show 0 ≤ x₀ - s by linarith)
  have P2 := mul_le_mul_of_nonneg_left B (show 0 ≤ t - x₀ by linarith)
  have : (t - s) * (ℓ - 1) ≤ (t - s) * slope u s t := by linarith
  exact le_of_mul_le_mul_left this (by linarith)

end StrictTop

/-! ## Lemme 4.2 : dérivabilité stricte dans `[-∞,∞]` -/

section StrictEReal

variable {c d : ℝ}

/-- **Lemme 4.2 sur un intervalle de type inférieur** : si les dérivées unilatérales de `u`
en `x₀` valent `p ∈ [-∞,∞]`, alors `k(s,t) ∈ W` pour `s < t` proches de `x₀`, pour tout
voisinage `W` de `p`. -/
lemma LowerFrame.strict_ereal (hF : LowerFrame u c d Θ) {x₀ : ℝ} (hx₀ : x₀ ∈ Icc c d)
    {p : EReal}
    (hR : x₀ < d → Tendsto (fun ρ => ((slope u x₀ (x₀ + ρ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 p))
    (hL : c < x₀ → Tendsto (fun ρ => ((slope u (x₀ - ρ) x₀ : ℝ) : EReal)) (𝓝[>] 0) (𝓝 p))
    {W : Set EReal} (hW : W ∈ 𝓝 p) :
    ∃ r > 0, ∀ s t, c ≤ s → s < t → t ≤ d → x₀ - r ≤ s → t ≤ x₀ + r →
      ((slope u s t : ℝ) : EReal) ∈ W := by
  induction p using EReal.rec with
  | coe p' =>
    -- cas p fini
    have hW' : ((↑) : ℝ → EReal) ⁻¹' W ∈ 𝓝 p' :=
      (EReal.tendsto_coe.mpr tendsto_id) hW
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW'
    obtain ⟨η, hη⟩ : ∃ η, η = min (ε / 8) 1 := ⟨_, rfl⟩
    have hηpos : 0 < η := by rw [hη]; exact lt_min (by linarith) one_pos
    have hη1 : η ≤ 1 := by rw [hη]; exact min_le_right _ _
    have hηε : η ≤ ε / 8 := by rw [hη]; exact min_le_left _ _
    obtain ⟨r, hr, H⟩ := hF.strict_real hx₀ (fun h => EReal.tendsto_coe.mp (hR h))
      (fun h => EReal.tendsto_coe.mp (hL h)) hηpos hη1
    refine ⟨r, hr, fun s t h1 h2 h3 h4 h5 => ?_⟩
    have hb := H s t h1 h2 h3 h4 h5
    have hmem : slope u s t ∈ Metric.ball p' ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hb.1, hb.2]
    exact hball hmem
  | top =>
    -- cas p = +∞
    obtain ⟨a', ha', hsub⟩ := nhds_top_basis.mem_iff.mp hW
    obtain ⟨m, hm1, -⟩ := EReal.lt_iff_exists_real_btwn.mp ha'
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = max m 0 + 2 := ⟨_, rfl⟩
    have hℓpos : 0 < ℓ := by rw [hℓ]; linarith [le_max_right m 0]
    have hℓm : m < ℓ - 1 := by rw [hℓ]; linarith [le_max_left m 0]
    obtain ⟨r, hr, H⟩ := hF.strict_top hx₀ hR hL hℓpos
    refine ⟨r, hr, fun s t h1 h2 h3 h4 h5 => hsub ?_⟩
    have hb := H s t h1 h2 h3 h4 h5
    show a' < ((slope u s t : ℝ) : EReal)
    exact hm1.trans (EReal.coe_lt_coe_iff.mpr (by linarith))
  | bot =>
    -- cas p = -∞ : symétrie (S₂)
    obtain ⟨a', ha', hsub⟩ := nhds_bot_basis.mem_iff.mp hW
    obtain ⟨m, -, hm2⟩ := EReal.lt_iff_exists_real_btwn.mp ha'
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = max (-m) 0 + 2 := ⟨_, rfl⟩
    have hℓpos : 0 < ℓ := by rw [hℓ]; linarith [le_max_right (-m) 0]
    have hℓm : 1 - ℓ < m := by rw [hℓ]; linarith [le_max_left (-m) 0]
    have hR' : c + d - x₀ < d → Tendsto (fun ρ => ((slope (fun y => u (c + d - y))
        (c + d - x₀) (c + d - x₀ + ρ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤) := fun h => by
      have hc : c < x₀ := by linarith
      simp only [slope_reflect u c d x₀, EReal.coe_neg]
      have := (continuous_neg.tendsto (⊥ : EReal)).comp (hL hc)
      rw [EReal.neg_bot] at this
      exact this
    have hL' : c < c + d - x₀ → Tendsto (fun ρ => ((slope (fun y => u (c + d - y))
        (c + d - x₀ - ρ) (c + d - x₀) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤) := fun h => by
      have hd : x₀ < d := by linarith
      simp only [slope_reflect' u c d x₀, EReal.coe_neg]
      have := (continuous_neg.tendsto (⊥ : EReal)).comp (hR hd)
      rw [EReal.neg_bot] at this
      exact this
    obtain ⟨r, hr, H⟩ := hF.reflect.strict_top ⟨by linarith [hx₀.2], by linarith [hx₀.1]⟩
      hR' hL' hℓpos
    refine ⟨r, hr, fun s t h1 h2 h3 h4 h5 => hsub ?_⟩
    have hb := H (c + d - t) (c + d - s) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
    rw [slope_reflect_gen] at hb
    show ((slope u s t : ℝ) : EReal) < a'
    exact (EReal.coe_lt_coe_iff.mpr (by linarith)).trans hm2

end StrictEReal

/-- **Lemme 4.2** sur `[a,b]` : si `u'(x₀) = p ∈ [-∞,∞]` (dérivées unilatérales égales
à `p` là où elles ont un sens), alors `k(s,t) ∈ W` pour `s < t` dans `[a,b]` proches de `x₀`,
pour tout voisinage `W` de `p`. -/
theorem GlobalFrame.strict_deriv (hG : GlobalFrame u f g a b Θ ρ₀) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc a b) {p : EReal}
    (hR : x₀ < b → Tendsto (fun ρ => ((slope u x₀ (x₀ + ρ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 p))
    (hL : a < x₀ → Tendsto (fun ρ => ((slope u (x₀ - ρ) x₀ : ℝ) : EReal)) (𝓝[>] 0) (𝓝 p))
    {W : Set EReal} (hW : W ∈ 𝓝 p) :
    ∃ r > 0, ∀ s t, a ≤ s → s < t → t ≤ b → x₀ - r ≤ s → t ≤ x₀ + r →
      ((slope u s t : ℝ) : EReal) ∈ W := by
  -- l'intervalle J = [c, d] = [x₀ - ρ₀/2, x₀ + ρ₀/2] ∩ [a, b]
  obtain ⟨c, hc⟩ : ∃ c, c = max a (x₀ - ρ₀ / 2) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = min b (x₀ + ρ₀ / 2) := ⟨_, rfl⟩
  have hρ := hG.ρpos
  have hac : a ≤ c := by rw [hc]; exact le_max_left _ _
  have hdb : d ≤ b := by rw [hd]; exact min_le_left _ _
  have hc2 : x₀ - ρ₀ / 2 ≤ c := by rw [hc]; exact le_max_right _ _
  have hd2 : d ≤ x₀ + ρ₀ / 2 := by rw [hd]; exact min_le_right _ _
  have hcx : c ≤ x₀ := by rw [hc]; exact max_le hx₀.1 (by linarith)
  have hxd : x₀ ≤ d := by rw [hd]; exact le_min hx₀.2 (by linarith)
  have hcd : c < d := by
    rw [hc, hd]
    exact lt_min (max_lt hG.lt (by linarith [hx₀.2])) (max_lt (by linarith [hx₀.1]) (by linarith))
  have hlen : d - c ≤ ρ₀ := by linarith
  have hRJ : x₀ < d → x₀ < b := fun h => lt_of_lt_of_le h hdb
  have hLJ : c < x₀ → a < x₀ := fun h => lt_of_le_of_lt hac h
  -- un s ≥ a proche de x₀ est ≥ c, un t ≤ b proche de x₀ est ≤ d
  have hsc : ∀ s r, r ≤ ρ₀ / 2 → a ≤ s → x₀ - r ≤ s → c ≤ s := fun s r hr h1 h2 => by
    rw [hc]; exact max_le h1 (by linarith)
  have htd : ∀ t r, r ≤ ρ₀ / 2 → t ≤ b → t ≤ x₀ + r → t ≤ d := fun t r hr h1 h2 => by
    rw [hd]; exact le_min h1 (by linarith)
  rcases hG.dich c d hac hcd hdb hlen with hLow | hUp
  · -- type inférieur
    obtain ⟨r, hr, H⟩ := (hG.lower c d hac hcd hdb hlen hLow).strict_ereal ⟨hcx, hxd⟩
      (fun h => hR (hRJ h)) (fun h => hL (hLJ h)) hW
    refine ⟨min r (ρ₀ / 2), lt_min hr (by linarith), fun s t h1 h2 h3 h4 h5 => ?_⟩
    have hm1 := min_le_left r (ρ₀ / 2)
    have hm2 := min_le_right r (ρ₀ / 2)
    exact H s t (hsc s _ hm2 h1 h4) h2 (htd t _ hm2 h3 h5) (by linarith) (by linarith)
  · -- type supérieur : on travaille avec -u (symétrie (S₁))
    have hW' : (fun y : EReal => -y) ⁻¹' W ∈ 𝓝 (-p) := by
      apply continuous_neg.continuousAt.preimage_mem_nhds
      show W ∈ 𝓝 (-(-p))
      rw [neg_neg]
      exact hW
    obtain ⟨r, hr, H⟩ := (hG.upper c d hac hcd hdb hlen hUp).strict_ereal ⟨hcx, hxd⟩
      (fun h => tendsto_neg_right (hR (hRJ h))) (fun h => tendsto_neg_left (hL (hLJ h))) hW'
    refine ⟨min r (ρ₀ / 2), lt_min hr (by linarith), fun s t h1 h2 h3 h4 h5 => ?_⟩
    have hm1 := min_le_left r (ρ₀ / 2)
    have hm2 := min_le_right r (ρ₀ / 2)
    have := H s t (hsc s _ hm2 h1 h4) h2 (htd t _ hm2 h3 h5) (by linarith) (by linarith)
    simp only [mem_preimage, slope_neg_fun, EReal.coe_neg, neg_neg] at this
    exact this

/-- **Assertion (ii) du Théorème 2.2** : `k(s,t) → u'(x₀)` quand `s, t → x₀`, `s < t`. -/
theorem GlobalFrame.strict_tendsto (hG : GlobalFrame u f g a b Θ ρ₀) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc a b) {p : EReal}
    (hR : x₀ < b → Tendsto (fun ρ => ((slope u x₀ (x₀ + ρ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 p))
    (hL : a < x₀ → Tendsto (fun ρ => ((slope u (x₀ - ρ) x₀ : ℝ) : EReal)) (𝓝[>] 0) (𝓝 p)) :
    Tendsto (fun st : ℝ × ℝ => ((slope u st.1 st.2 : ℝ) : EReal))
      (𝓝[{st : ℝ × ℝ | st.1 < st.2 ∧ st.1 ∈ Icc a b ∧ st.2 ∈ Icc a b}] (x₀, x₀)) (𝓝 p) := by
  intro W hW
  obtain ⟨r, hr, H⟩ := hG.strict_deriv hx₀ hR hL hW
  rw [mem_map, mem_nhdsWithin]
  refine ⟨Ioo (x₀ - r) (x₀ + r) ×ˢ Ioo (x₀ - r) (x₀ + r), isOpen_Ioo.prod isOpen_Ioo,
    ⟨⟨show x₀ - r < x₀ by linarith, show x₀ < x₀ + r by linarith⟩,
      ⟨show x₀ - r < x₀ by linarith, show x₀ < x₀ + r by linarith⟩⟩, ?_⟩
  rintro ⟨s, t⟩ ⟨⟨⟨hs1, hs2⟩, ht1, ht2⟩, hst, hsab, htab⟩
  exact H s t hsab.1 hst htab.2 hs1.le ht2.le

/-! ## Le théorème principal dans le cadre abstrait -/

/-- **Théorème 2.2, forme abstraite** : sous (O_f) et (O_g), il existe `u' : ℝ → [-∞,∞]`
qui est la dérivée de `u` relativement à `[a,b]` en tout point de `[a,b]`, qui est continue
sur `[a,b]`, et qui vérifie les assertions (i) et (ii). -/
theorem GlobalFrame.main (hG : GlobalFrame u f g a b Θ ρ₀)
    (hOf : ∀ x ∈ Ioo a b, u x = f x → dLowerLeft f x ≤ dUpperRight f x)
    (hOg : ∀ x ∈ Ioo a b, u x = g x → dLowerRight g x ≤ dUpperLeft g x) :
    ∃ u' : ℝ → EReal,
      (∀ x ∈ Icc a b, HasEDerivWithinIcc a b u (u' x) x) ∧
      ContinuousOn u' (Icc a b) ∧
      (∀ x ∈ Ioo a b, u x = f x → u' x = dLowerLeft f x ∧ u' x = dUpperRight f x) ∧
      (∀ x ∈ Ioo a b, u x = g x → u' x = dLowerRight g x ∧ u' x = dUpperLeft g x) ∧
      (∀ x₀ ∈ Icc a b,
        Tendsto (fun st : ℝ × ℝ => eslope u st.1 st.2)
          (𝓝[{st : ℝ × ℝ | st.1 < st.2 ∧ st.1 ∈ Icc a b ∧ st.2 ∈ Icc a b}] (x₀, x₀))
          (𝓝 (u' x₀))) := by
  -- construction de u' : valeur commune des dérivées unilatérales
  have hex : ∀ x : ℝ, ∃ p : EReal,
      (x ∈ Ico a b → Tendsto (fun ρ => ((slope u x (x + ρ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 p)) ∧
      (x ∈ Ioc a b → Tendsto (fun ρ => ((slope u (x - ρ) x : ℝ) : EReal)) (𝓝[>] 0) (𝓝 p)) := by
    intro x
    by_cases h1 : x ∈ Ico a b
    · obtain ⟨p, hp⟩ := hG.exists_right h1
      by_cases h2 : x ∈ Ioc a b
      · obtain ⟨q, hq⟩ := hG.exists_left h2
        have peq := (hG.one_sided_eq hOf hOg ⟨h2.1, h1.2⟩ hp hq).1
        exact ⟨p, fun _ => hp, fun _ => peq ▸ hq⟩
      · exact ⟨p, fun _ => hp, fun h => absurd h h2⟩
    · by_cases h2 : x ∈ Ioc a b
      · obtain ⟨q, hq⟩ := hG.exists_left h2
        exact ⟨q, fun h => absurd h h1, fun _ => hq⟩
      · exact ⟨0, fun h => absurd h h1, fun h => absurd h h2⟩
  choose u' hu'R hu'L using hex
  -- (ii) : dérivabilité stricte
  have hstrict : ∀ x₀ ∈ Icc a b,
      Tendsto (fun st : ℝ × ℝ => ((slope u st.1 st.2 : ℝ) : EReal))
        (𝓝[{st : ℝ × ℝ | st.1 < st.2 ∧ st.1 ∈ Icc a b ∧ st.2 ∈ Icc a b}] (x₀, x₀))
        (𝓝 (u' x₀)) := fun x₀ hx₀ =>
    hG.strict_tendsto hx₀ (fun h => hu'R x₀ ⟨hx₀.1, h⟩) (fun h => hu'L x₀ ⟨h, hx₀.2⟩)
  refine ⟨u', ?_, ?_, ?_, ?_, hstrict⟩
  · -- u' est la dérivée de u relativement à [a,b]
    intro x hx
    have hmap : Tendsto (fun t => (min x t, max x t)) (𝓝[Icc a b \ {x}] x)
        (𝓝[{st : ℝ × ℝ | st.1 < st.2 ∧ st.1 ∈ Icc a b ∧ st.2 ∈ Icc a b}] (x, x)) := by
      apply tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Continuous (fun t : ℝ => (min x t, max x t)) := by fun_prop
        have := hc.tendsto x
        simp only [min_self, max_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        rcases (show t ≠ x from ht.2).lt_or_gt with h | h
        · rw [min_eq_right h.le, max_eq_left h.le]
          exact ⟨h, ht.1, hx⟩
        · rw [min_eq_left h.le, max_eq_right h.le]
          exact ⟨h, hx, ht.1⟩
    unfold HasEDerivWithinIcc
    refine ((hstrict x hx).comp hmap).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rcases (show t ≠ x from ht.2).lt_or_gt with h | h
    · simp only [Function.comp_apply, min_eq_right h.le, max_eq_left h.le, eslope]
      rw [slope_comm]
    · simp only [Function.comp_apply, min_eq_left h.le, max_eq_right h.le, eslope]
  · -- continuité de u'
    intro x₀ hx₀
    rw [ContinuousWithinAt, (closed_nhds_basis (u' x₀)).tendsto_right_iff]
    rintro W ⟨hW, hWc⟩
    obtain ⟨r, hr, H⟩ := hG.strict_deriv hx₀ (fun h => hu'R x₀ ⟨hx₀.1, h⟩)
      (fun h => hu'L x₀ ⟨h, hx₀.2⟩) hW
    have hnear : ∀ᶠ x in 𝓝[Icc a b] x₀, x ∈ Ioo (x₀ - r) (x₀ + r) :=
      nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) (by linarith))
    filter_upwards [hnear, self_mem_nhdsWithin] with x hx1 hx2
    by_cases hxb : x < b
    · -- u'(x) est limite des pentes k(x, x + ρ), qui sont dans le fermé W
      have hlim := hu'R x ⟨hx2.1, hxb⟩
      apply hWc.mem_of_tendsto hlim
      have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < min (b - x) (x₀ + r - x) :=
        nhdsWithin_le_nhds (eventually_lt_nhds (lt_min (by linarith) (by linarith [hx1.2])))
      filter_upwards [self_mem_nhdsWithin, hsmall] with ρ hρ1 hρ2
      have hρ : 0 < ρ := hρ1
      have m1 := min_le_left (b - x) (x₀ + r - x)
      have m2 := min_le_right (b - x) (x₀ + r - x)
      exact H x (x + ρ) hx2.1 (by linarith) (by linarith) (by linarith [hx1.1]) (by linarith)
    · -- x = b : u'(x) est limite des pentes k(x - ρ, x)
      have hxb' : x = b := le_antisymm hx2.2 (not_lt.mp hxb)
      have hax : a < x := by rw [hxb']; exact hG.lt
      have hlim := hu'L x ⟨hax, hx2.2⟩
      apply hWc.mem_of_tendsto hlim
      have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < min (x - a) (x - (x₀ - r)) :=
        nhdsWithin_le_nhds (eventually_lt_nhds (lt_min (by linarith) (by linarith [hx1.1])))
      filter_upwards [self_mem_nhdsWithin, hsmall] with ρ hρ1 hρ2
      have hρ : 0 < ρ := hρ1
      have m1 := min_le_left (x - a) (x - (x₀ - r))
      have m2 := min_le_right (x - a) (x - (x₀ - r))
      exact H (x - ρ) x (by linarith) (by linarith) hx2.2 (by linarith) (by linarith [hx1.2])
  · -- assertion (i), contact avec f
    intro x hx h1
    exact (hG.one_sided_eq hOf hOg hx (hu'R x ⟨hx.1.le, hx.2⟩) (hu'L x ⟨hx.1, hx.2.le⟩)).2.1 h1
  · -- assertion (i), contact avec g
    intro x hx h2
    exact (hG.one_sided_eq hOf hOg hx (hu'R x ⟨hx.1.le, hx.2⟩) (hu'L x ⟨hx.1, hx.2.le⟩)).2.2 h2

end TonelliObstacle
