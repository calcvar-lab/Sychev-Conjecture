import Project.Section2

/-!
# Preuve du théorème principal (Théorème 2.2)

On assemble : le cadre global (`global_frame`, Section 2) et le théorème de la Section 4
(`GlobalFrame.main`). Il reste à voir que `u'` n'est infinie que sur un ensemble
négligeable : en presque tout point intérieur, `u` est dérivable (différentiation de
Lebesgue), donc `u'` y vaut la dérivée usuelle, qui est finie.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace TonelliObstacle

/-- En un point intérieur où `u` est dérivable, la dérivée de Tonelli est la dérivée usuelle. -/
lemma eDeriv_eq_of_hasDerivAt {u : ℝ → ℝ} {a b x d : ℝ} {p : EReal} (hx : x ∈ Ioo a b)
    (hp : HasEDerivWithinIcc a b u p x) (hd : HasDerivAt u d x) : p = (d : EReal) := by
  have h0 : Tendsto (fun t => eslope u x t) (𝓝[Icc a b \ {x}] x) (𝓝 p) := hp
  have h1 : Tendsto (fun t => eslope u x t) (𝓝[Icc a b \ {x}] x) (𝓝 (d : EReal)) := by
    have h := EReal.tendsto_coe.mpr (hasDerivAt_iff_tendsto_slope.mp hd)
    exact h.mono_left (nhdsWithin_mono _ (fun y hy => hy.2))
  have : (𝓝[Icc a b \ {x}] x).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    have hsub : Ioo x b ⊆ Icc a b \ {x} := fun y hy =>
      ⟨⟨by linarith [hx.1, hy.1], hy.2.le⟩, fun h => by
        rw [mem_singleton_iff] at h
        linarith [hy.1]⟩
    apply closure_mono hsub
    rw [closure_Ioo hx.2.ne]
    exact left_mem_Icc.mpr hx.2.le
  exact tendsto_nhds_unique h0 h1

/-- **Théorème 2.2** (démontré).  -/
theorem main_theorem (a b A B : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (f g u : ℝ → ℝ)
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x < g x)
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH1 : HypH1 a b L) (hH2 : HypH2 a b L)
    (hu : IsFiniteEnergySolution a b A B L f g u)
    (hOf : ∀ x ∈ Ioo a b, u x = f x → dLowerLeft f x ≤ dUpperRight f x)
    (hOg : ∀ x ∈ Ioo a b, u x = g x → dLowerRight g x ≤ dUpperLeft g x) :
    ∃ u' : ℝ → EReal, IsTonelliDeriv a b u u' ∧
      (∀ x ∈ Ioo a b, u x = f x → u' x = dLowerLeft f x ∧ u' x = dUpperRight f x) ∧
      (∀ x ∈ Ioo a b, u x = g x → u' x = dLowerRight g x ∧ u' x = dUpperLeft g x) ∧
      (∀ x₀ ∈ Icc a b,
        Tendsto (fun p : ℝ × ℝ => eslope u p.1 p.2)
          (𝓝[{p : ℝ × ℝ | p.1 < p.2 ∧ p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b}] (x₀, x₀))
          (𝓝 (u' x₀))) := by
  obtain ⟨Θ, ρ₀, hG⟩ := global_frame hab hf hg hfg hL hH1 hH2 hu
  obtain ⟨u', hder, hcont, hcf, hcg, hstrict⟩ := hG.main hOf hOg
  refine ⟨u', ⟨hder, hcont, ?_⟩, hcf, hcg, hstrict⟩
  obtain ⟨⟨hW, -⟩, -⟩ := hu
  obtain ⟨gg, hgg, hrep⟩ := hW
  have hae := W11_ae_hasDerivAt hab.le hgg hrep
  have hnull : volume {x | ¬ (x ∈ Ioo a b → HasDerivAt u (gg x) x)} = 0 := ae_iff.mp hae
  refine measure_mono_null ?_
    (measure_union_null (measure_union_null (measure_singleton a) (measure_singleton b)) hnull)
  intro x hxS
  obtain ⟨hx, hinf⟩ := hxS
  by_cases hxa : x = a
  · exact Or.inl (Or.inl hxa)
  by_cases hxb : x = b
  · exact Or.inl (Or.inr hxb)
  refine Or.inr ?_
  show ¬ (x ∈ Ioo a b → HasDerivAt u (gg x) x)
  intro hP
  have hxI : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  have heq := eDeriv_eq_of_hasDerivAt hxI (hder x hx) (hP hxI)
  rcases hinf with h | h <;> rw [heq] at h
  · exact EReal.coe_ne_top _ h
  · exact EReal.coe_ne_bot _ h

/-! ## Corollaires -/

/-- Si les pentes de `f` en `x` ont une limite `p` (dans `[-∞,∞]`), les quatre dérivés
de Dini de `f` en `x` valent `p`. -/
lemma dini_of_tendsto {f : ℝ → ℝ} {x : ℝ} {p : EReal}
    (h : Tendsto (fun t => eslope f x t) (𝓝[≠] x) (𝓝 p)) :
    dUpperRight f x = p ∧ dLowerRight f x = p ∧ dUpperLeft f x = p ∧ dLowerLeft f x = p := by
  have hmR : Tendsto (fun t => x + t) (𝓝[>] (0 : ℝ)) (𝓝[≠] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_const_add x).tendsto' 0 x (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      show x + t ≠ x
      intro h'
      linarith
  have hmL : Tendsto (fun t => x - t) (𝓝[>] (0 : ℝ)) (𝓝[≠] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_sub_left x).tendsto' 0 x (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      show x - t ≠ x
      intro h'
      linarith
  have hR : Tendsto (fun t => eslope f x (x + t)) (𝓝[>] 0) (𝓝 p) := h.comp hmR
  have hL : Tendsto (fun t => eslope f (x - t) x) (𝓝[>] 0) (𝓝 p) := by
    have e : (fun t => eslope f (x - t) x) = fun t => eslope f x (x - t) := by
      funext t
      unfold eslope
      rw [slope_comm]
    rw [e]
    exact h.comp hmL
  exact ⟨hR.limsup_eq, hR.liminf_eq, hL.limsup_eq, hL.liminf_eq⟩

/-- **Corollaire 2.3** (démontré). -/
theorem sychev_conjecture (a b A B : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (f g u : ℝ → ℝ)
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x < g x)
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH1 : HypH1 a b L) (hH2 : HypH2 a b L)
    (hf' : ∀ x ∈ Ioo a b, ∃ p : EReal, Tendsto (fun t => eslope f x t) (𝓝[≠] x) (𝓝 p))
    (hg' : ∀ x ∈ Ioo a b, ∃ p : EReal, Tendsto (fun t => eslope g x t) (𝓝[≠] x) (𝓝 p))
    (hu : IsFiniteEnergySolution a b A B L f g u) :
    TonelliRegular a b u := by
  have hOf : ∀ x ∈ Ioo a b, u x = f x → dLowerLeft f x ≤ dUpperRight f x := by
    intro x hx _
    obtain ⟨p, hp⟩ := hf' x hx
    obtain ⟨h1, -, -, h4⟩ := dini_of_tendsto hp
    exact h4.le.trans h1.symm.le
  have hOg : ∀ x ∈ Ioo a b, u x = g x → dLowerRight g x ≤ dUpperLeft g x := by
    intro x hx _
    obtain ⟨p, hp⟩ := hg' x hx
    obtain ⟨-, h2, h3, -⟩ := dini_of_tendsto hp
    exact h2.le.trans h3.symm.le
  obtain ⟨u', hT, -⟩ := main_theorem a b A B L f g u hab hf hg hfg hL hH1 hH2 hu hOf hOg
  obtain ⟨⟨hW, -⟩, -⟩ := hu
  exact ⟨hW, u', hT⟩

/-- **Corollaire 2.4** (démontré). -/
theorem C1_near_contact (a b A B : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (f g u : ℝ → ℝ)
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x < g x)
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH1 : HypH1 a b L) (hH2 : HypH2 a b L)
    (hfd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hgd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x)
    (hu : IsFiniteEnergySolution a b A B L f g u)
    (x₀ : ℝ) (hx₀ : x₀ ∈ Ioo a b) (hcontact : u x₀ = f x₀ ∨ u x₀ = g x₀) :
    ∃ r > 0, ContDiffOn ℝ 1 u (Ioo (x₀ - r) (x₀ + r)) := by
  have hfT : ∀ x ∈ Ioo a b,
      Tendsto (fun t => eslope f x t) (𝓝[≠] x) (𝓝 ((deriv f x : ℝ) : EReal)) :=
    fun x hx => EReal.tendsto_coe.mpr (hasDerivAt_iff_tendsto_slope.mp (hfd x hx).hasDerivAt)
  have hgT : ∀ x ∈ Ioo a b,
      Tendsto (fun t => eslope g x t) (𝓝[≠] x) (𝓝 ((deriv g x : ℝ) : EReal)) :=
    fun x hx => EReal.tendsto_coe.mpr (hasDerivAt_iff_tendsto_slope.mp (hgd x hx).hasDerivAt)
  have hOf : ∀ x ∈ Ioo a b, u x = f x → dLowerLeft f x ≤ dUpperRight f x := by
    intro x hx _
    obtain ⟨h1, -, -, h4⟩ := dini_of_tendsto (hfT x hx)
    exact h4.le.trans h1.symm.le
  have hOg : ∀ x ∈ Ioo a b, u x = g x → dLowerRight g x ≤ dUpperLeft g x := by
    intro x hx _
    obtain ⟨-, h2, h3, -⟩ := dini_of_tendsto (hgT x hx)
    exact h2.le.trans h3.symm.le
  obtain ⟨u', ⟨hder, hcont, -⟩, hcf, hcg, -⟩ :=
    main_theorem a b A B L f g u hab hf hg hfg hL hH1 hH2 hu hOf hOg
  -- u'(x₀) est finie (c'est la dérivée de l'obstacle)
  have hfin : u' x₀ ∈ Ioo (⊥ : EReal) ⊤ := by
    rcases hcontact with h | h
    · obtain ⟨-, -, -, h4⟩ := dini_of_tendsto (hfT x₀ hx₀)
      rw [(hcf x₀ hx₀ h).1, h4]
      exact ⟨EReal.bot_lt_coe _, EReal.coe_lt_top _⟩
    · obtain ⟨-, h2, -, -⟩ := dini_of_tendsto (hgT x₀ hx₀)
      rw [(hcg x₀ hx₀ h).1, h2]
      exact ⟨EReal.bot_lt_coe _, EReal.coe_lt_top _⟩
  -- par continuité, u' est finie près de x₀
  have hca : ContinuousAt u' x₀ :=
    (hcont x₀ (Ioo_subset_Icc_self hx₀)).continuousAt (Icc_mem_nhds hx₀.1 hx₀.2)
  have hS : {x | u' x ∈ Ioo (⊥ : EReal) ⊤} ∩ Ioo a b ∈ 𝓝 x₀ :=
    inter_mem (hca.preimage_mem_nhds (isOpen_Ioo.mem_nhds hfin)) (Ioo_mem_nhds hx₀.1 hx₀.2)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hS
  rw [Real.ball_eq_Ioo] at hball
  refine ⟨r, hr, ?_⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ → ℝ, v = fun x => (u' x).toReal := ⟨_, rfl⟩
  have hxab : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), x ∈ Ioo a b := fun x hx => (hball hx).2
  have hcoe : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), u' x = ((v x : ℝ) : EReal) := by
    intro x hx
    have h : u' x ∈ Ioo (⊥ : EReal) ⊤ := (hball hx).1
    rw [hv]
    exact (EReal.coe_toReal (ne_top_of_lt h.2) (ne_bot_of_gt h.1)).symm
  -- u est dérivable, de dérivée v, sur l'intervalle
  have hderiv : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), HasDerivAt u (v x) x := by
    intro x hx
    have hxI := hxab x hx
    have h0 : Tendsto (fun t => ((slope u x t : ℝ) : EReal)) (𝓝[Icc a b \ {x}] x) (𝓝 (u' x)) :=
      hder x (Ioo_subset_Icc_self hxI)
    rw [hcoe x hx] at h0
    have h1 : Tendsto (slope u x) (𝓝[Icc a b \ {x}] x) (𝓝 (v x)) := EReal.tendsto_coe.mp h0
    have hmem : Icc a b ∈ 𝓝[{x}ᶜ] x := mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hxI.1 hxI.2)
    rw [sdiff_eq, nhdsWithin_inter_of_mem hmem] at h1
    exact hasDerivAt_iff_tendsto_slope.mpr h1
  -- v est continue sur l'intervalle
  have hvc : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), ContinuousAt v x := by
    intro x hx
    have hxI := hxab x hx
    have hc : Tendsto u' (𝓝 x) (𝓝 (u' x)) :=
      (hcont x (Ioo_subset_Icc_self hxI)).continuousAt (Icc_mem_nhds hxI.1 hxI.2)
    have hev : u' =ᶠ[𝓝 x] fun y => ((v y : ℝ) : EReal) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy using hcoe y hy
    rw [hcoe x hx] at hc
    exact EReal.tendsto_coe.mp (hc.congr' hev)
  rw [contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn]
  refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, ?_⟩
  refine ContinuousOn.congr (fun x hx => (hvc x hx).continuousWithinAt) ?_
  intro x hx
  exact (hderiv x hx).hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffOn x hx)

/-! ## Compléments aux corollaires : énoncés complets de l'article -/

/-- À l'intérieur de `[a,b]`, `𝓝[[a,b] \ {x}] x = 𝓝[≠] x`. -/
lemma nhdsWithin_Icc_diff {a b x : ℝ} (hx : x ∈ Ioo a b) :
    𝓝[Icc a b \ {x}] x = 𝓝[≠] x := by
  have hmem : Icc a b ∈ 𝓝[{x}ᶜ] x := mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
  rw [sdiff_eq, nhdsWithin_inter_of_mem hmem]

/-- Une fonction ayant la régularité de Tonelli a une dérivée dans `[-∞,∞]` en tout point
de `]a,b[`. -/
lemma tendsto_slope_of_tonelli {a b : ℝ} {f : ℝ → ℝ} (hf : TonelliRegular a b f) :
    ∀ x ∈ Ioo a b, ∃ p : EReal, Tendsto (fun t => eslope f x t) (𝓝[≠] x) (𝓝 p) := by
  obtain ⟨-, f', hder, -, -⟩ := hf
  intro x hx
  refine ⟨f' x, ?_⟩
  have h : Tendsto (fun t => eslope f x t) (𝓝[Icc a b \ {x}] x) (𝓝 (f' x)) :=
    hder x (Ioo_subset_Icc_self hx)
  rwa [nhdsWithin_Icc_diff hx] at h

/-- **Corollaire 2.3**, avec `u' = f'` sur `{u = f} ∩ ]a,b[` et `u' = g'` sur `{u = g} ∩ ]a,b[`
(où `f'(x)` est la limite `p` des pentes de `f` en `x`). -/
theorem sychev_conjecture_deriv (a b A B : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (f g u : ℝ → ℝ)
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x < g x)
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH1 : HypH1 a b L) (hH2 : HypH2 a b L)
    (hf' : ∀ x ∈ Ioo a b, ∃ p : EReal, Tendsto (fun t => eslope f x t) (𝓝[≠] x) (𝓝 p))
    (hg' : ∀ x ∈ Ioo a b, ∃ p : EReal, Tendsto (fun t => eslope g x t) (𝓝[≠] x) (𝓝 p))
    (hu : IsFiniteEnergySolution a b A B L f g u) :
    ∃ u' : ℝ → EReal, IsTonelliDeriv a b u u' ∧
      (∀ x ∈ Ioo a b, u x = f x → ∀ p : EReal,
        Tendsto (fun t => eslope f x t) (𝓝[≠] x) (𝓝 p) → u' x = p) ∧
      (∀ x ∈ Ioo a b, u x = g x → ∀ p : EReal,
        Tendsto (fun t => eslope g x t) (𝓝[≠] x) (𝓝 p) → u' x = p) := by
  have hOf : ∀ x ∈ Ioo a b, u x = f x → dLowerLeft f x ≤ dUpperRight f x := by
    intro x hx _
    obtain ⟨p, hp⟩ := hf' x hx
    obtain ⟨h1, -, -, h4⟩ := dini_of_tendsto hp
    exact h4.le.trans h1.symm.le
  have hOg : ∀ x ∈ Ioo a b, u x = g x → dLowerRight g x ≤ dUpperLeft g x := by
    intro x hx _
    obtain ⟨p, hp⟩ := hg' x hx
    obtain ⟨-, h2, h3, -⟩ := dini_of_tendsto hp
    exact h2.le.trans h3.symm.le
  obtain ⟨u', hT, hcf, hcg, -⟩ := main_theorem a b A B L f g u hab hf hg hfg hL hH1 hH2 hu hOf hOg
  refine ⟨u', hT, fun x hx hc p hp => ?_, fun x hx hc p hp => ?_⟩
  · rw [(hcf x hx hc).1]
    exact (dini_of_tendsto hp).2.2.2
  · rw [(hcg x hx hc).1]
    exact (dini_of_tendsto hp).2.1

/-- **Corollaire 2.3**, cas particulier `f, g ∈ W^{1,1}_T([a,b])`. -/
theorem sychev_conjecture_of_tonelli (a b A B : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (f g u : ℝ → ℝ)
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x < g x)
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH1 : HypH1 a b L) (hH2 : HypH2 a b L)
    (hfT : TonelliRegular a b f) (hgT : TonelliRegular a b g)
    (hu : IsFiniteEnergySolution a b A B L f g u) :
    TonelliRegular a b u :=
  sychev_conjecture a b A B L f g u hab hf hg hfg hL hH1 hH2
    (tendsto_slope_of_tonelli hfT) (tendsto_slope_of_tonelli hgT) hu

/-! ### Solutions sans hypothèse d'énergie finie -/

open Classical in
/-- L'énergie `𝒥_L(u;[a,b]) ∈ ]-∞,+∞]` : `+∞` si la densité n'est pas intégrable
(la densité est minorée sur `𝒜_{f,g}`, Remarque 2.1(b)). -/
def energyE (a b : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (u : ℝ → ℝ) : EReal :=
  if FiniteEnergy a b L u then ((energy a b L u : ℝ) : EReal) else ⊤

/-- `u ∈ 𝒮_{f,g}` : `u` minimise `𝒥_L(·;[a,b])` sur `𝒜_{f,g}`. -/
def IsSolution (a b A B : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (f g u : ℝ → ℝ) : Prop :=
  u ∈ Admissible a b A B f g ∧
    ∀ v ∈ Admissible a b A B f g, energyE a b L u ≤ energyE a b L v

lemma energyE_of_finite {a b : ℝ} {L : ℝ → ℝ → ℝ → ℝ} {u : ℝ → ℝ}
    (h : FiniteEnergy a b L u) : energyE a b L u = ((energy a b L u : ℝ) : EReal) := by
  unfold energyE
  rw [if_pos h]

lemma energyE_of_not_finite {a b : ℝ} {L : ℝ → ℝ → ℝ → ℝ} {u : ℝ → ℝ}
    (h : ¬ FiniteEnergy a b L u) : energyE a b L u = ⊤ := by
  unfold energyE
  rw [if_neg h]

/-- La notion `IsFiniteEnergySolution` utilisée partout est bien
« `u ∈ 𝒮_{f,g}` et `𝒥_L(u;[a,b]) < ∞` ». -/
theorem isFiniteEnergySolution_iff {a b A B : ℝ} {L : ℝ → ℝ → ℝ → ℝ} {f g u : ℝ → ℝ} :
    IsFiniteEnergySolution a b A B L f g u ↔
      IsSolution a b A B L f g u ∧ FiniteEnergy a b L u := by
  constructor
  · rintro ⟨hA, hE, hmin⟩
    refine ⟨⟨hA, fun v hv => ?_⟩, hE⟩
    rw [energyE_of_finite hE]
    by_cases hvE : FiniteEnergy a b L v
    · rw [energyE_of_finite hvE]
      exact EReal.coe_le_coe_iff.mpr (hmin v hv hvE)
    · rw [energyE_of_not_finite hvE]
      exact le_top
  · rintro ⟨⟨hA, hmin⟩, hE⟩
    refine ⟨hA, hE, fun v hv hvE => ?_⟩
    have h := hmin v hv
    rw [energyE_of_finite hE, energyE_of_finite hvE] at h
    exact EReal.coe_le_coe_iff.mp h

/-- Si `inf_𝒜 𝒥_L(·;[a,b]) < ∞`, toute solution est d'énergie finie. -/
theorem finiteEnergy_of_inf_lt_top {a b A B : ℝ} {L : ℝ → ℝ → ℝ → ℝ} {f g u : ℝ → ℝ}
    (hinf : ⨅ v ∈ Admissible a b A B f g, energyE a b L v < ⊤)
    (hu : IsSolution a b A B L f g u) : IsFiniteEnergySolution a b A B L f g u := by
  obtain ⟨v, hv⟩ := iInf_lt_iff.mp hinf
  obtain ⟨hvA, hvlt⟩ := iInf_lt_iff.mp hv
  have huE : FiniteEnergy a b L u := by
    by_contra h
    have h1 := hu.2 v hvA
    rw [energyE_of_not_finite h] at h1
    exact lt_irrefl _ (h1.trans_lt hvlt)
  exact isFiniteEnergySolution_iff.mpr ⟨hu, huE⟩

/-- **Corollaire 2.3**, dernière assertion : si `inf_𝒜 𝒥_L < ∞`, *toute* solution a la
régularité partielle de Tonelli. -/
theorem sychev_conjecture_all_solutions (a b A B : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (f g u : ℝ → ℝ)
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x < g x)
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH1 : HypH1 a b L) (hH2 : HypH2 a b L)
    (hf' : ∀ x ∈ Ioo a b, ∃ p : EReal, Tendsto (fun t => eslope f x t) (𝓝[≠] x) (𝓝 p))
    (hg' : ∀ x ∈ Ioo a b, ∃ p : EReal, Tendsto (fun t => eslope g x t) (𝓝[≠] x) (𝓝 p))
    (hinf : ⨅ v ∈ Admissible a b A B f g, energyE a b L v < ⊤)
    (hu : IsSolution a b A B L f g u) :
    TonelliRegular a b u :=
  sychev_conjecture a b A B L f g u hab hf hg hfg hL hH1 hH2 hf' hg'
    (finiteEnergy_of_inf_lt_top hinf hu)

/-! ### Corollaire 2.4 : l'ensemble singulier -/

/-- **Corollaire 2.4** : l'ensemble singulier `{u' = ±∞}` est fermé et contenu dans
`{a,b} ∪ {f < u < g}`. -/
theorem C1_singular_set (a b A B : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (f g u : ℝ → ℝ)
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x < g x)
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH1 : HypH1 a b L) (hH2 : HypH2 a b L)
    (hfd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hgd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x)
    (hu : IsFiniteEnergySolution a b A B L f g u) :
    ∃ u' : ℝ → EReal, IsTonelliDeriv a b u u' ∧
      IsClosed {x ∈ Icc a b | u' x = ⊤ ∨ u' x = ⊥} ∧
      {x ∈ Icc a b | u' x = ⊤ ∨ u' x = ⊥} ⊆ {a, b} ∪ {x | f x < u x ∧ u x < g x} := by
  have hfT : ∀ x ∈ Ioo a b,
      Tendsto (fun t => eslope f x t) (𝓝[≠] x) (𝓝 ((deriv f x : ℝ) : EReal)) :=
    fun x hx => EReal.tendsto_coe.mpr (hasDerivAt_iff_tendsto_slope.mp (hfd x hx).hasDerivAt)
  have hgT : ∀ x ∈ Ioo a b,
      Tendsto (fun t => eslope g x t) (𝓝[≠] x) (𝓝 ((deriv g x : ℝ) : EReal)) :=
    fun x hx => EReal.tendsto_coe.mpr (hasDerivAt_iff_tendsto_slope.mp (hgd x hx).hasDerivAt)
  have hOf : ∀ x ∈ Ioo a b, u x = f x → dLowerLeft f x ≤ dUpperRight f x := by
    intro x hx _
    obtain ⟨h1, -, -, h4⟩ := dini_of_tendsto (hfT x hx)
    exact h4.le.trans h1.symm.le
  have hOg : ∀ x ∈ Ioo a b, u x = g x → dLowerRight g x ≤ dUpperLeft g x := by
    intro x hx _
    obtain ⟨-, h2, h3, -⟩ := dini_of_tendsto (hgT x hx)
    exact h2.le.trans h3.symm.le
  obtain ⟨u', ⟨hder, hcont, hvol⟩, hcf, hcg, -⟩ :=
    main_theorem a b A B L f g u hab hf hg hfg hL hH1 hH2 hu hOf hOg
  obtain ⟨⟨-, -, -, hfgu⟩, -, -⟩ := hu
  refine ⟨u', ⟨hder, hcont, hvol⟩, ?_, ?_⟩
  · have hcl : IsClosed (Icc a b ∩ u' ⁻¹' {⊤, ⊥}) :=
      hcont.preimage_isClosed_of_isClosed isClosed_Icc
        ((Set.finite_singleton (⊥ : EReal)).insert ⊤).isClosed
    convert hcl using 1
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_insert_iff,
      mem_singleton_iff]
  · rintro x ⟨hx, hinf⟩
    by_cases hxa : x = a
    · exact Or.inl (Or.inl hxa)
    by_cases hxb : x = b
    · exact Or.inl (Or.inr hxb)
    have hxI : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
    have hfin : ∀ p : ℝ, u' x = (p : EReal) → False := by
      intro p hp
      rw [hp] at hinf
      rcases hinf with h | h
      · exact EReal.coe_ne_top _ h
      · exact EReal.coe_ne_bot _ h
    refine Or.inr ⟨?_, ?_⟩
    · rcases (hfgu x hx).1.lt_or_eq with h | h
      · exact h
      · exfalso
        obtain ⟨-, -, -, h4⟩ := dini_of_tendsto (hfT x hxI)
        exact hfin _ ((hcf x hxI h.symm).1.trans h4)
    · rcases (hfgu x hx).2.lt_or_eq with h | h
      · exact h
      · exfalso
        obtain ⟨-, h2, -, -⟩ := dini_of_tendsto (hgT x hxI)
        exact hfin _ ((hcg x hxI h).1.trans h2)

/-- **Corollaire 2.4** (énoncé complet) : régularité de Tonelli, ensemble singulier fermé
contenu dans `{a,b} ∪ {f < u < g}`, et `u` de classe `C¹` près de tout point de contact. -/
theorem C1_corollary (a b A B : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (f g u : ℝ → ℝ)
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x < g x)
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH1 : HypH1 a b L) (hH2 : HypH2 a b L)
    (hfd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hgd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x)
    (hu : IsFiniteEnergySolution a b A B L f g u) :
    TonelliRegular a b u ∧
      (∃ u' : ℝ → EReal, IsTonelliDeriv a b u u' ∧
        IsClosed {x ∈ Icc a b | u' x = ⊤ ∨ u' x = ⊥} ∧
        {x ∈ Icc a b | u' x = ⊤ ∨ u' x = ⊥} ⊆ {a, b} ∪ {x | f x < u x ∧ u x < g x}) ∧
      (∀ x₀ ∈ Ioo a b, (u x₀ = f x₀ ∨ u x₀ = g x₀) →
        ∃ r > 0, ContDiffOn ℝ 1 u (Ioo (x₀ - r) (x₀ + r))) := by
  have hf' : ∀ x ∈ Ioo a b, ∃ p : EReal, Tendsto (fun t => eslope f x t) (𝓝[≠] x) (𝓝 p) :=
    fun x hx => ⟨_, EReal.tendsto_coe.mpr
      (hasDerivAt_iff_tendsto_slope.mp (hfd x hx).hasDerivAt)⟩
  have hg' : ∀ x ∈ Ioo a b, ∃ p : EReal, Tendsto (fun t => eslope g x t) (𝓝[≠] x) (𝓝 p) :=
    fun x hx => ⟨_, EReal.tendsto_coe.mpr
      (hasDerivAt_iff_tendsto_slope.mp (hgd x hx).hasDerivAt)⟩
  exact ⟨sychev_conjecture a b A B L f g u hab hf hg hfg hL hH1 hH2 hf' hg' hu,
    C1_singular_set a b A B L f g u hab hf hg hfg hL hH1 hH2 hfd hgd hu,
    fun x₀ hx₀ hc => C1_near_contact a b A B L f g u hab hf hg hfg hL hH1 hH2 hfd hgd hu
      x₀ hx₀ hc⟩

end TonelliObstacle
