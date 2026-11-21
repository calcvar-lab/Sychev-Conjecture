import Project.Main

/-!
# Remarques de l'article : énoncés complémentaires et exemples

Ce fichier formalise les affirmations des remarques de l'article qui ne sont pas couvertes
par `Project/Main.lean` :

* **Remarque 2.1** : (a) continuité de `L_v` sous (H₂) ; (b) l'énergie est bien définie dans
  `]-∞, +∞]` (justification de `energyE`) ; (c) la Hölder-continuité en toutes les variables
  implique (H₁).
* **Remarque 2.5** : pour des obstacles de classe `C¹`, toute solution est d'énergie finie ;
  le Corollaire 2.4 s'applique donc à toutes les solutions.
* **Remarque 2.6(a)** : obstacles convexes ou semi-convexes (resp. concaves ou semi-concaves)
  ⟹ (O_f) (resp. (O_g)).
* **Remarque 2.6(b)** : les conditions (O_f) et (O_g) ne peuvent pas être supprimées
  (`f(x) = -|x|`, resp. `g(x) = |x|`, avec `L = v²`).
* **Remarque 2.6(c)** : l'hypothèse d'énergie finie ne peut pas être supprimée
  (`f(x) = (x - a)^{1/3}`, `g = f + 1`, et la solution oscillante
  `v = f + λ φ(x)(x - c)²(2 + sin(1/(x - c)))`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Interval

noncomputable section

namespace TonelliObstacle

/-! ## Remarque 2.1(a) : continuité de `L_v` -/

/-- **Remarque 2.1(a)** : sous (H₂), `L_v` est continue sur `[a,b] × ℝ × ℝ`. Par la formule
de Taylor, `L_v` est la limite localement uniforme des taux d'accroissement continus
`(L(P, v + h) - L(P, v)) / h`. -/
theorem Lv_continuousOn {a b : ℝ} {L Lv Lvv : ℝ → ℝ → ℝ → ℝ}
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hLvv : ContinuousOn (fun p : ℝ × ℝ × ℝ => Lvv p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hd : ∀ x ∈ Icc a b, ∀ w v : ℝ, HasDerivAt (fun v => L x w v) (Lv x w v) v ∧
      HasDerivAt (fun v => Lv x w v) (Lvv x w v) v) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Lv p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))) := by
  rintro ⟨x₀, w₀, v₀⟩ hp₀
  have hx₀ : x₀ ∈ Icc a b := hp₀.1
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  -- borne de `L_vv` sur un compact
  have hK : IsCompact (Icc a b ×ˢ (Icc (w₀ - 1) (w₀ + 1) ×ˢ Icc (v₀ - 2) (v₀ + 2))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (hLvv.mono (fun p hp => ⟨hp.1, mem_univ _⟩))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (x₀, w₀, v₀)
    ⟨hx₀, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩)
  -- Taylor : le taux d'accroissement approche `L_v` à `M h / 2` près
  have hT : ∀ x ∈ Icc a b, ∀ w ∈ Icc (w₀ - 1) (w₀ + 1), ∀ v ∈ Icc (v₀ - 1) (v₀ + 1),
      ∀ h ∈ Ioc (0 : ℝ) 1,
        |(L x w (v + h) - L x w v) / h - Lv x w v| ≤ M / 2 * h := by
    intro x hx w hw v hv h hh
    have h1 : ∀ s, HasDerivAt (fun s => L x w s) (Lv x w s) s := fun s => (hd x hx w s).1
    have h2 : ∀ s, HasDerivAt (fun s => Lv x w s) (Lvv x w s) s := fun s => (hd x hx w s).2
    have hb : ∀ s ∈ Icc (v₀ - 2) (v₀ + 2), |Lvv x w s| ≤ M := fun s hs => by
      simpa using hM (x, w, s) ⟨hx, hw, hs⟩
    have hvI : v ∈ Icc (v₀ - 2) (v₀ + 2) := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hvhI : v + h ∈ Icc (v₀ - 2) (v₀ + 2) :=
      ⟨by linarith [hv.1, hh.1], by linarith [hv.2, hh.2]⟩
    have lo := taylor_lower_on (φ := fun s => L x w s) (φd := fun s => Lv x w s)
      (φdd := fun s => Lvv x w s) (μ := -M)
      h1 h2 (fun s hs => by linarith [neg_abs_le (Lvv x w s), hb s hs]) hvI hvhI
    have up := taylor_upper_on (φ := fun s => L x w s) (φd := fun s => Lv x w s)
      (φdd := fun s => Lvv x w s) (Λ := M)
      h1 h2 (fun s hs => by linarith [le_abs_self (Lvv x w s), hb s hs]) hvI hvhI
    have hh0 : 0 < h := hh.1
    have e : (L x w (v + h) - L x w v) / h - Lv x w v =
        ((L x w (v + h) - L x w v) - Lv x w v * h) / h := by
      field_simp
    rw [e, abs_div, abs_of_pos hh0, div_le_iff₀ hh0, abs_le]
    simp only [add_sub_cancel_left] at lo up
    constructor
    · linarith
    · linarith
  -- choix de `h`
  obtain ⟨h, hh, hhM⟩ : ∃ h : ℝ, h ∈ Ioc (0 : ℝ) 1 ∧ M / 2 * h < ε / 3 := by
    refine ⟨min 1 (ε / (6 * (M + 1))),
      ⟨lt_min one_pos (by positivity), min_le_left _ _⟩, ?_⟩
    have h1 : min 1 (ε / (6 * (M + 1))) ≤ ε / (6 * (M + 1)) := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ M / 2 by positivity)
    have h3 : M / 2 * (ε / (6 * (M + 1))) ≤ (M + 1) * (ε / (6 * (M + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h4 : (M + 1) * (ε / (6 * (M + 1))) = ε / 6 := by
      field_simp
    linarith
  -- continuité du taux d'accroissement
  have hDc : ContinuousOn
      (fun p : ℝ × ℝ × ℝ => (L p.1 p.2.1 (p.2.2 + h) - L p.1 p.2.1 p.2.2) / h)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))) := by
    refine ContinuousOn.div_const (ContinuousOn.sub ?_ hL) h
    have hm : MapsTo (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1, p.2.2 + h))
        (Icc a b ×ˢ (univ : Set (ℝ × ℝ))) (Icc a b ×ˢ (univ : Set (ℝ × ℝ))) :=
      fun p hp => ⟨hp.1, mem_univ _⟩
    exact hL.comp (Continuous.continuousOn (by fun_prop)) hm
  obtain ⟨δ₁, hδ₁, hD⟩ :=
    Metric.continuousWithinAt_iff.mp (hDc _ hp₀) (ε / 3) (by positivity)
  refine ⟨min δ₁ 1, lt_min hδ₁ one_pos, fun {p} hp hdist => ?_⟩
  obtain ⟨x, w, v⟩ := p
  have hd1 : dist (x, w, v) (x₀, w₀, v₀) < δ₁ := hdist.trans_le (min_le_left _ _)
  have hd2 : dist (x, w, v) (x₀, w₀, v₀) < 1 := hdist.trans_le (min_le_right _ _)
  have hD1 := hD hp hd1
  have hx : x ∈ Icc a b := hp.1
  simp only [Prod.dist_eq, Real.dist_eq, max_lt_iff] at hd2 hD1 ⊢
  obtain ⟨-, hw, hv⟩ := hd2
  have e1 := hT x hx w ⟨by linarith [(abs_lt.mp hw).1], by linarith [(abs_lt.mp hw).2]⟩
    v ⟨by linarith [(abs_lt.mp hv).1], by linarith [(abs_lt.mp hv).2]⟩ h hh
  have e0 := hT x₀ hx₀ w₀ ⟨by linarith, by linarith⟩ v₀ ⟨by linarith, by linarith⟩ h hh
  rw [abs_le] at e1 e0
  rw [abs_lt] at hD1 ⊢
  constructor <;> linarith [e1.1, e1.2, e0.1, e0.2, hD1.1, hD1.2]

/-- **Remarque 2.1(a)** : sous (H₂), la dérivée `L_v` existe et est continue sur
`[a,b] × ℝ × ℝ`. -/
theorem hypH2_Lv_continuousOn {a b : ℝ} {L : ℝ → ℝ → ℝ → ℝ}
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH2 : HypH2 a b L) :
    ∃ Lv : ℝ → ℝ → ℝ → ℝ,
      (∀ x ∈ Icc a b, ∀ w v : ℝ, HasDerivAt (fun v => L x w v) (Lv x w v) v) ∧
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Lv p.1 p.2.1 p.2.2)
        (Icc a b ×ˢ (univ : Set (ℝ × ℝ))) := by
  obtain ⟨Lv, Lvv, μ, -, hc, hH⟩ := hH2
  exact ⟨Lv, fun x hx w v => (hH x hx w v).1,
    Lv_continuousOn hL hc (fun x hx w v => ⟨(hH x hx w v).1, (hH x hx w v).2.1⟩)⟩

/-! ## Remarque 2.1(b) : l'énergie est bien définie dans `]-∞, +∞]` -/

/-- La densité d'énergie `x ↦ L(x, v(x), v'(x))` est mesurable sur `[a,b]`. -/
lemma energyDensity_aestronglyMeasurable {a b : ℝ} (hab : a ≤ b) {L : ℝ → ℝ → ℝ → ℝ}
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    {v : ℝ → ℝ} (hv : ContinuousOn v (Icc a b)) :
    AEStronglyMeasurable (energyDensity L v) (volume.restrict (Icc a b)) := by
  set P : ℝ → ℝ := fun x => (projIcc a b hab x : ℝ) with hP
  have hPc : Continuous P := continuous_subtype_val.comp continuous_projIcc
  have hPm : ∀ x, P x ∈ Icc a b := fun x => (projIcc a b hab x).2
  have hvc : Continuous (fun x => v (P x)) := hv.comp_continuous hPc hPm
  have hLc : Continuous (fun p : ℝ × ℝ × ℝ => L (P p.1) p.2.1 p.2.2) :=
    hL.comp_continuous (f := fun p : ℝ × ℝ × ℝ => (P p.1, p.2.1, p.2.2)) (by fun_prop)
      (fun p => ⟨hPm p.1, mem_univ _⟩)
  have hF : Measurable (fun x => L (P x) (v (P x)) (deriv v x)) :=
    hLc.measurable.comp (measurable_id.prodMk (hvc.measurable.prodMk (measurable_deriv v)))
  refine hF.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have : P x = x := by simp [hP, projIcc_of_mem hab hx]
  simp [energyDensity, this]

lemma enorm_eq_ofReal_add_ofReal_neg (r : ℝ) :
    ‖r‖ₑ = ENNReal.ofReal r + ENNReal.ofReal (-r) := by
  rcases le_total 0 r with h | h
  · rw [Real.enorm_eq_ofReal h, ENNReal.ofReal_of_nonpos (by linarith : -r ≤ 0), add_zero]
  · rw [← enorm_neg, Real.enorm_eq_ofReal (by linarith : 0 ≤ -r),
      ENNReal.ofReal_of_nonpos h, zero_add]

/-- **Remarque 2.1(b)** : pour `v ∈ W^{1,1}([a,b])` (en particulier pour `v ∈ 𝒜_{f,g}`), la
densité d'énergie est minorée sur `[a,b]`, sa partie négative est intégrable, et
`energyE a b L v` est exactement l'intégrale de Lebesgue `∫ L(x,v,v') ∈ ]-∞, +∞]`,
i.e. `∫ (partie positive) - ∫ (partie négative)`. -/
theorem energyE_eq_lintegral {a b : ℝ} (hab : a ≤ b) {L : ℝ → ℝ → ℝ → ℝ}
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH2 : HypH2 a b L) {v : ℝ → ℝ} (hv : IsW11 a b v) :
    (∃ K : ℝ, ∀ x ∈ Icc a b, -K ≤ energyDensity L v x) ∧
      (∫⁻ x in Icc a b, ENNReal.ofReal (-energyDensity L v x)) < ∞ ∧
      energyE a b L v =
        ((∫⁻ x in Icc a b, ENNReal.ofReal (energyDensity L v x) : ℝ≥0∞) : EReal) -
          ((∫⁻ x in Icc a b, ENNReal.ofReal (-energyDensity L v x) : ℝ≥0∞) : EReal) := by
  have hvc := W11_continuousOn hab hv
  have hmeas := energyDensity_aestronglyMeasurable hab hL hvc
  obtain ⟨Mv, hMv⟩ : ∃ M, ∀ x ∈ Icc a b, |v x| ≤ M := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hvc
    exact ⟨M, fun x hx => by simpa using hM x hx⟩
  obtain ⟨μ, hμ, K, hK⟩ := exists_lower_bound (m₁ := -Mv) (m₂ := Mv) hL hH2
  have hlow : ∀ x ∈ Icc a b, -K ≤ energyDensity L v x := by
    intro x hx
    have h1 := hK x hx (v x) (abs_le.mp (hMv x hx)) (deriv v x)
    have h2 : 0 ≤ μ / 4 * deriv v x ^ 2 := by positivity
    simp only [energyDensity]
    linarith
  have hneg : (∫⁻ x in Icc a b, ENNReal.ofReal (-energyDensity L v x)) < ∞ := by
    calc (∫⁻ x in Icc a b, ENNReal.ofReal (-energyDensity L v x))
        ≤ ∫⁻ x in Icc a b, ENNReal.ofReal K :=
          setLIntegral_mono' measurableSet_Icc
            (fun x hx => ENNReal.ofReal_le_ofReal (by linarith [hlow x hx]))
      _ = ENNReal.ofReal K * volume (Icc a b) := setLIntegral_const _ _
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)
  refine ⟨⟨K, hlow⟩, hneg, ?_⟩
  have hN : (∫⁻ x in Icc a b, ENNReal.ofReal (-energyDensity L v x)) ≠ ∞ := hneg.ne
  by_cases hE : FiniteEnergy a b L v
  · rw [energyE_of_finite hE]
    have hint : ∫ x in a..b, energyDensity L v x = ∫ x in Icc a b, energyDensity L v x := by
      rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
    have hP : (∫⁻ x in Icc a b, ENNReal.ofReal (energyDensity L v x)) ≠ ∞ := by
      have hfin := hasFiniteIntegral_iff_enorm.mp hE.2
      refine (lt_of_le_of_lt (lintegral_mono (fun x => ?_)) hfin).ne
      rw [enorm_eq_ofReal_add_ofReal_neg]
      exact le_self_add
    rw [energy, hint, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hE, EReal.coe_sub,
      EReal.coe_ennreal_toReal hP, EReal.coe_ennreal_toReal hN]
  · rw [energyE_of_not_finite hE]
    have hP : (∫⁻ x in Icc a b, ENNReal.ofReal (energyDensity L v x)) = ∞ := by
      by_contra hP
      apply hE
      refine ⟨hmeas, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      calc ∫⁻ x in Icc a b, ‖energyDensity L v x‖ₑ
          = (∫⁻ x in Icc a b, ENNReal.ofReal (energyDensity L v x)) +
              ∫⁻ x in Icc a b, ENNReal.ofReal (-energyDensity L v x) := by
            simp_rw [enorm_eq_ofReal_add_ofReal_neg]
            exact lintegral_add_left' hmeas.aemeasurable.ennreal_ofReal _
        _ < ∞ := ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hP, hneg⟩
    rw [hP, EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hN, EReal.top_sub_coe]

/-! ## Remarque 2.1(c) : la Hölder-continuité en toutes les variables implique (H₁) -/

/-- Hölder-continuité locale de `L` en toutes ses variables, comme dans [Man18]. -/
def HypHolderAll (a b : ℝ) (L : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ R : ℝ, ∃ C : ℝ, 0 < C ∧ ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
    ∀ x₁ ∈ Icc a b, ∀ x₂ ∈ Icc a b, ∀ w₁ w₂ v₁ v₂ : ℝ,
      |w₁| ≤ R → |w₂| ≤ R → |v₁| ≤ R → |v₂| ≤ R →
        |L x₁ w₁ v₁ - L x₂ w₂ v₂| ≤ C * (|x₁ - x₂| + |w₁ - w₂| + |v₁ - v₂|) ^ α

/-- **Remarque 2.1(c)** : (H₁) est plus faible que la Hölder-continuité en toutes les
variables. -/
theorem hypH1_of_holderAll {a b : ℝ} {L : ℝ → ℝ → ℝ → ℝ} (h : HypHolderAll a b L) :
    HypH1 a b L := by
  intro R
  obtain ⟨C, hC, α, hα, hα1, hH⟩ := h R
  refine ⟨C, hC, α, hα, hα1, fun x₁ hx₁ x₂ hx₂ w₁ w₂ v hw₁ hw₂ hv => ?_⟩
  have := hH x₁ hx₁ x₂ hx₂ w₁ w₂ v v hw₁ hw₂ hv hv
  simpa using this

/-! ## Remarque 2.5 : obstacles de classe `C¹` -/

/-- Une fonction de classe `C¹` sur `[a,b]` est dans `W^{1,1}([a,b])`. -/
lemma isW11_of_contDiffOn {a b : ℝ} (hab : a < b) {h : ℝ → ℝ}
    (hh : ContDiffOn ℝ 1 h (Icc a b)) : IsW11 a b h := by
  have hc' : ContinuousOn (derivWithin h (Icc a b)) (Icc a b) :=
    hh.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  have hint : ∀ x ∈ Icc a b, IntervalIntegrable (derivWithin h (Icc a b)) volume a x :=
    fun x hx => (hc'.mono (Icc_subset_Icc_right hx.2)).intervalIntegrable_of_Icc hx.1
  refine ⟨derivWithin h (Icc a b), hint b ⟨hab.le, le_rfl⟩, fun x hx => ?_⟩
  have hcont : ContinuousOn h (Icc a x) := hh.continuousOn.mono (Icc_subset_Icc_right hx.2)
  have hder : ∀ t ∈ Ioo a x, HasDerivWithinAt h (derivWithin h (Icc a b) t) (Ioi t) t := by
    intro t ht
    have htI : t ∈ Ioo a b := ⟨ht.1, ht.2.trans_le hx.2⟩
    have hdiff : DifferentiableWithinAt ℝ h (Icc a b) t :=
      (hh.differentiableOn (by norm_num)) t (Ioo_subset_Icc_self htI)
    exact (hdiff.hasDerivWithinAt.hasDerivAt (Icc_mem_nhds htI.1 htI.2)).hasDerivWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx.1 hcont hder (hint x hx)]
  ring

/-- Une fonction de classe `C¹` sur `[a,b]` est d'énergie finie. -/
lemma finiteEnergy_of_contDiffOn {a b : ℝ} (hab : a < b) {L : ℝ → ℝ → ℝ → ℝ}
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    {h : ℝ → ℝ} (hh : ContDiffOn ℝ 1 h (Icc a b)) : FiniteEnergy a b L h := by
  have hc' : ContinuousOn (derivWithin h (Icc a b)) (Icc a b) :=
    hh.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hc'
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn hh.continuousOn
  have hK : IsCompact (Icc a b ×ˢ (Icc (-H) H ×ˢ Icc (-D) D)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hL.mono (fun p hp => ⟨hp.1, mem_univ _⟩))
  refine ⟨energyDensity_aestronglyMeasurable hab.le hL hh.continuousOn,
    HasFiniteIntegral.restrict_of_bounded (C := C) (by simp) ?_⟩
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [ae_ne_pt a, ae_ne_pt b] with x hxa hxb hx
  have hxI : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  have hdx : deriv h x = derivWithin h (Icc a b) x := by
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hxI.1 hxI.2)]
  have hb := hC (x, h x, deriv h x)
    ⟨hx, abs_le.mp (by simpa using hH x hx), by rw [hdx]; exact abs_le.mp (by simpa using hD x hx)⟩
  simpa [energyDensity] using hb

/-- Si `f, g` sont de classe `C¹` sur `[a,b]` et `𝒜_{f,g} ≠ ∅`, alors `𝒜_{f,g}` contient une
fonction de classe `C¹` (en particulier lipschitzienne) : `h = f + θ (g - f)`, `θ` affine. -/
lemma exists_contDiffOn_admissible {a b A B : ℝ} (hab : a < b) {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) (hg : ContDiffOn ℝ 1 g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x < g x) (hne : (Admissible a b A B f g).Nonempty) :
    ∃ h ∈ Admissible a b A B f g, ContDiffOn ℝ 1 h (Icc a b) := by
  obtain ⟨u, -, huA, huB, hu⟩ := hne
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hga := sub_pos.mpr (hfg a ha)
  have hgb := sub_pos.mpr (hfg b hb)
  obtain ⟨θa, hθa⟩ : ∃ θ, θ = (A - f a) / (g a - f a) := ⟨_, rfl⟩
  obtain ⟨θb, hθb⟩ : ∃ θ, θ = (B - f b) / (g b - f b) := ⟨_, rfl⟩
  have hθa0 : 0 ≤ θa := by
    rw [hθa]; exact div_nonneg (by linarith [(hu a ha).1]) hga.le
  have hθa1 : θa ≤ 1 := by
    rw [hθa, div_le_one hga]; linarith [(hu a ha).2]
  have hθb0 : 0 ≤ θb := by
    rw [hθb]; exact div_nonneg (by linarith [(hu b hb).1]) hgb.le
  have hθb1 : θb ≤ 1 := by
    rw [hθb, div_le_one hgb]; linarith [(hu b hb).2]
  set θ : ℝ → ℝ := fun x => θa + (θb - θa) * ((x - a) / (b - a)) with hθ
  have hθc : ContDiff ℝ 1 θ :=
    contDiff_const.add (contDiff_const.mul ((contDiff_id.sub contDiff_const).div_const _))
  have hθI : ∀ x ∈ Icc a b, 0 ≤ θ x ∧ θ x ≤ 1 := by
    intro x hx
    have hs0 : 0 ≤ (x - a) / (b - a) := div_nonneg (by linarith [hx.1]) (by linarith)
    have hs1 : (x - a) / (b - a) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith [hx.2]
    simp only [hθ]
    constructor <;> nlinarith
  refine ⟨fun x => f x + θ x * (g x - f x), ⟨?_, ?_, ?_, ?_⟩,
    hf.add (hθc.contDiffOn.mul (hg.sub hf))⟩
  · exact isW11_of_contDiffOn hab (hf.add (hθc.contDiffOn.mul (hg.sub hf)))
  · have : θ a = θa := by simp [hθ]
    simp only [this, hθa]
    field_simp
    ring
  · have : θ b = θb := by
      simp only [hθ]
      rw [div_self (by linarith : b - a ≠ 0)]
      ring
    simp only [this, hθb]
    field_simp
    ring
  · intro x hx
    have := hθI x hx
    have hgf := sub_pos.mpr (hfg x hx)
    constructor <;> nlinarith

/-- **Remarque 2.5** : si `f, g` sont de classe `C¹` sur `[a,b]`, toute solution est
d'énergie finie (`𝒜_{f,g}` contient une fonction lipschitzienne). -/
theorem isFiniteEnergySolution_of_C1 {a b A B : ℝ} {L : ℝ → ℝ → ℝ → ℝ} {f g u : ℝ → ℝ}
    (hab : a < b)
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hf : ContDiffOn ℝ 1 f (Icc a b)) (hg : ContDiffOn ℝ 1 g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x < g x) (hu : IsSolution a b A B L f g u) :
    IsFiniteEnergySolution a b A B L f g u := by
  obtain ⟨h, hA, hh⟩ := exists_contDiffOn_admissible hab hf hg hfg ⟨u, hu.1⟩
  refine finiteEnergy_of_inf_lt_top ?_ hu
  calc ⨅ v ∈ Admissible a b A B f g, energyE a b L v ≤ energyE a b L h := iInf₂_le h hA
    _ = ((energy a b L h : ℝ) : EReal) :=
      energyE_of_finite (finiteEnergy_of_contDiffOn hab hL hh)
    _ < ⊤ := EReal.coe_lt_top _

/-- **Corollaire 2.4 et Remarque 2.5** : pour des obstacles de classe `C¹` sur `[a,b]`,
*toute* solution a la régularité partielle de Tonelli, son ensemble singulier est fermé et
contenu dans `{a,b} ∪ {f < u < g}`, et elle est de classe `C¹` près des points de contact. -/
theorem C1_corollary_all_solutions (a b A B : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (f g u : ℝ → ℝ)
    (hab : a < b)
    (hf : ContDiffOn ℝ 1 f (Icc a b)) (hg : ContDiffOn ℝ 1 g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x < g x)
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH1 : HypH1 a b L) (hH2 : HypH2 a b L)
    (hu : IsSolution a b A B L f g u) :
    TonelliRegular a b u ∧
      (∃ u' : ℝ → EReal, IsTonelliDeriv a b u u' ∧
        IsClosed {x ∈ Icc a b | u' x = ⊤ ∨ u' x = ⊥} ∧
        {x ∈ Icc a b | u' x = ⊤ ∨ u' x = ⊥} ⊆ {a, b} ∪ {x | f x < u x ∧ u x < g x}) ∧
      (∀ x₀ ∈ Ioo a b, (u x₀ = f x₀ ∨ u x₀ = g x₀) →
        ∃ r > 0, ContDiffOn ℝ 1 u (Ioo (x₀ - r) (x₀ + r))) := by
  have hdiff : ∀ {k : ℝ → ℝ}, ContDiffOn ℝ 1 k (Icc a b) →
      ∀ x ∈ Ioo a b, DifferentiableAt ℝ k x := fun hk x hx =>
    ((hk.differentiableOn (by norm_num)) x (Ioo_subset_Icc_self hx)).differentiableAt
      (Icc_mem_nhds hx.1 hx.2)
  exact C1_corollary a b A B L f g u hab hf.continuousOn hg.continuousOn hfg hL hH1 hH2
    (hdiff hf) (hdiff hg) (isFiniteEnergySolution_of_C1 hab hL hf hg hfg hu)

/-! ## Remarque 2.6(a) : obstacles convexes et semi-convexes -/

/-- Lemme clé : si `P t ≤ R s` pour `t, s ∈ ]0, ε[` et si `Q` et `S` ont la même limite
finie `ℓ` en `0⁺`, alors `liminf (P + Q) ≤ limsup (R + S)` en `0⁺`. -/
lemma liminf_le_limsup_of_split {P Q R S : ℝ → ℝ} {ε ℓ : ℝ} (hε : 0 < ε)
    (hPR : ∀ t ∈ Ioo 0 ε, ∀ s ∈ Ioo 0 ε, P t ≤ R s)
    (hQ : Tendsto Q (𝓝[>] 0) (𝓝 ℓ)) (hS : Tendsto S (𝓝[>] 0) (𝓝 ℓ)) :
    liminf (fun t => ((P t + Q t : ℝ) : EReal)) (𝓝[>] 0) ≤
      limsup (fun s => ((R s + S s : ℝ) : EReal)) (𝓝[>] 0) := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨r₁, h₁, h₁'⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  obtain ⟨r₂, h₂, h₂'⟩ := EReal.lt_iff_exists_real_btwn.1 h₁'
  have hr : r₁ < r₂ := EReal.coe_lt_coe_iff.mp h₂
  have hS1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), ((R s + S s : ℝ) : EReal) < r₁ :=
    eventually_lt_of_limsup_lt h₁
  have hP2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), (r₂ : EReal) < ((P t + Q t : ℝ) : EReal) :=
    eventually_lt_of_lt_liminf h₂'
  obtain ⟨η, hη⟩ : ∃ η, η = (r₂ - r₁) / 2 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; linarith
  have hQη : ∀ᶠ t in 𝓝[>] (0 : ℝ), Q t < ℓ + η := hQ (Iio_mem_nhds (by linarith))
  have hSη : ∀ᶠ s in 𝓝[>] (0 : ℝ), ℓ - η < S s := hS (Ioi_mem_nhds (by linarith))
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 ε := Ioo_mem_nhdsGT hε
  obtain ⟨t, htP, htQ, ht⟩ := (hP2.and (hQη.and hsmall)).exists
  obtain ⟨s, hsR, hsS, hs⟩ := (hS1.and (hSη.and hsmall)).exists
  have h0 := hPR t ht s hs
  have a1 := EReal.coe_lt_coe_iff.mp htP
  have a2 := EReal.coe_lt_coe_iff.mp hsR
  linarith

/-- Les pentes à droite et à gauche d'une fonction dérivable en `x` tendent vers sa dérivée. -/
lemma tendsto_slopes_of_hasDerivAt {ψ : ℝ → ℝ} {x d : ℝ} (h : HasDerivAt ψ d x) :
    Tendsto (fun t => slope ψ x (x + t)) (𝓝[>] 0) (𝓝 d) ∧
      Tendsto (fun t => slope ψ (x - t) x) (𝓝[>] 0) (𝓝 d) := by
  have h0 := hasDerivAt_iff_tendsto_slope.mp h
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
  refine ⟨h0.comp hmR, ?_⟩
  have e : (fun t => slope ψ (x - t) x) = fun t => slope ψ x (x - t) := by
    funext t
    rw [slope_comm]
  rw [e]
  exact h0.comp hmL

lemma slope_add_fun (φ ψ : ℝ → ℝ) (s t : ℝ) :
    slope (fun y => φ y + ψ y) s t = slope φ s t + slope ψ s t := by
  simp only [slope_def_field]
  rw [← add_div]
  congr 1
  ring

/-- **Remarque 2.6(a), obstacle inférieur.** Si `f` est semi-convexe près de `x`, i.e.
`f + (c/2) y²` est convexe sur `]x - ε, x + ε[`, alors `D₋f(x) ≤ D⁺f(x)`
(`c = 0` : cas convexe). -/
theorem dini_lower_of_semiconvex {f : ℝ → ℝ} {x ε c : ℝ} (hε : 0 < ε)
    (hconv : ConvexOn ℝ (Ioo (x - ε) (x + ε)) (fun y => f y + c / 2 * y ^ 2)) :
    dLowerLeft f x ≤ dUpperRight f x := by
  set φ : ℝ → ℝ := fun y => f y + c / 2 * y ^ 2 with hφ
  set ψ : ℝ → ℝ := fun y => -(c / 2) * y ^ 2 with hψ
  have hf : ∀ y, f y = φ y + ψ y := fun y => by simp only [hφ, hψ]; ring
  have hd : HasDerivAt ψ (-(c / 2) * (2 * x)) x := by
    have := (hasDerivAt_pow 2 x).const_mul (-(c / 2))
    simpa [hψ] using this
  obtain ⟨hR, hL⟩ := tendsto_slopes_of_hasDerivAt hd
  have hfun : f = fun y => φ y + ψ y := funext hf
  have eL : (fun t => eslope f (x - t) x) =
      fun t => ((slope φ (x - t) x + slope ψ (x - t) x : ℝ) : EReal) := by
    funext t
    rw [eslope, hfun, slope_add_fun]
  have eR : (fun t => eslope f x (x + t)) =
      fun t => ((slope φ x (x + t) + slope ψ x (x + t) : ℝ) : EReal) := by
    funext t
    rw [eslope, hfun, slope_add_fun]
  unfold dLowerLeft dUpperRight
  rw [eL, eR]
  refine liminf_le_limsup_of_split hε (fun t ht s hs => ?_) hL hR
  have h1 := hconv.slope_mono_adjacent (x := x - t) (y := x) (z := x + s)
    ⟨by linarith [ht.2], by linarith [ht.1]⟩ ⟨by linarith [hs.1], by linarith [hs.2]⟩
    (by linarith [ht.1]) (by linarith [hs.1])
  simp only [slope_def_field]
  convert h1 using 2

/-- **Remarque 2.6(a), obstacle supérieur.** Si `g` est semi-concave près de `x`, i.e.
`g - (c/2) y²` est concave sur `]x - ε, x + ε[`, alors `D₊g(x) ≤ D⁻g(x)`
(`c = 0` : cas concave). -/
theorem dini_upper_of_semiconcave {g : ℝ → ℝ} {x ε c : ℝ} (hε : 0 < ε)
    (hconc : ConcaveOn ℝ (Ioo (x - ε) (x + ε)) (fun y => g y - c / 2 * y ^ 2)) :
    dLowerRight g x ≤ dUpperLeft g x := by
  set φ : ℝ → ℝ := fun y => g y - c / 2 * y ^ 2 with hφ
  set ψ : ℝ → ℝ := fun y => c / 2 * y ^ 2 with hψ
  have hg : ∀ y, g y = φ y + ψ y := fun y => by simp [hφ, hψ]
  have hd : HasDerivAt ψ (c / 2 * (2 * x)) x := by
    have := (hasDerivAt_pow 2 x).const_mul (c / 2)
    simpa [hψ] using this
  obtain ⟨hR, hL⟩ := tendsto_slopes_of_hasDerivAt hd
  have hfun : g = fun y => φ y + ψ y := funext hg
  have eL : (fun t => eslope g (x - t) x) =
      fun t => ((slope φ (x - t) x + slope ψ (x - t) x : ℝ) : EReal) := by
    funext t
    rw [eslope, hfun, slope_add_fun]
  have eR : (fun t => eslope g x (x + t)) =
      fun t => ((slope φ x (x + t) + slope ψ x (x + t) : ℝ) : EReal) := by
    funext t
    rw [eslope, hfun, slope_add_fun]
  unfold dLowerRight dUpperLeft
  rw [eL, eR]
  refine liminf_le_limsup_of_split hε (fun t ht s hs => ?_) hR hL
  have h1 := hconc.slope_anti_adjacent (x := x - s) (y := x) (z := x + t)
    ⟨by linarith [hs.2], by linarith [hs.1]⟩ ⟨by linarith [ht.1], by linarith [ht.2]⟩
    (by linarith [hs.1]) (by linarith [ht.1])
  simp only [slope_def_field]
  convert h1 using 2

/-- **Remarque 2.6(a)** : si `f` est semi-convexe près de chaque point de contact avec `f`,
la condition (O_f) est satisfaite. -/
theorem Of_of_semiconvex {a b : ℝ} {f u : ℝ → ℝ}
    (h : ∀ x ∈ Ioo a b, u x = f x → ∃ ε > 0, ∃ c : ℝ,
      ConvexOn ℝ (Ioo (x - ε) (x + ε)) (fun y => f y + c / 2 * y ^ 2)) :
    ∀ x ∈ Ioo a b, u x = f x → dLowerLeft f x ≤ dUpperRight f x := by
  intro x hx hc
  obtain ⟨ε, hε, c, hconv⟩ := h x hx hc
  exact dini_lower_of_semiconvex hε hconv

/-- **Remarque 2.6(a)** : si `g` est semi-concave près de chaque point de contact avec `g`,
la condition (O_g) est satisfaite. -/
theorem Og_of_semiconcave {a b : ℝ} {g u : ℝ → ℝ}
    (h : ∀ x ∈ Ioo a b, u x = g x → ∃ ε > 0, ∃ c : ℝ,
      ConcaveOn ℝ (Ioo (x - ε) (x + ε)) (fun y => g y - c / 2 * y ^ 2)) :
    ∀ x ∈ Ioo a b, u x = g x → dLowerRight g x ≤ dUpperLeft g x := by
  intro x hx hc
  obtain ⟨ε, hε, c, hconc⟩ := h x hx hc
  exact dini_upper_of_semiconcave hε hconc

/-! ## Remarque 2.6(b) : les conditions (O_f) et (O_g) ne peuvent pas être supprimées -/

/-- Le lagrangien `L(x,w,v) = v²`. -/
def Lsq : ℝ → ℝ → ℝ → ℝ := fun _ _ v => v ^ 2

lemma Lsq_continuousOn (a b : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Lsq p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))) := by
  unfold Lsq
  exact Continuous.continuousOn (by fun_prop)

lemma Lsq_H1 (a b : ℝ) : HypH1 a b Lsq := by
  intro R
  refine ⟨1, one_pos, 1, one_pos, le_rfl, fun x₁ _ x₂ _ w₁ w₂ v _ _ _ => ?_⟩
  simp only [Lsq, sub_self, abs_zero, Real.rpow_one, one_mul]
  positivity

lemma Lsq_H2 (a b : ℝ) : HypH2 a b Lsq := by
  refine ⟨fun _ _ v => 2 * v, fun _ _ _ => 2, 2, two_pos, continuousOn_const,
    fun x _ w v => ⟨?_, ?_, le_rfl⟩⟩
  · simpa [Lsq] using hasDerivAt_pow 2 v
  · simpa using (hasDerivAt_id v).const_mul (2 : ℝ)

lemma energyDensity_Lsq (v : ℝ → ℝ) (x : ℝ) : energyDensity Lsq v x = deriv v x ^ 2 := rfl

lemma intervalIntegrable_of_Icc {f : ℝ → ℝ} {a b c d : ℝ} (h : IntegrableOn f (Icc a b))
    (hc : a ≤ c) (hcd : c ≤ d) (hd : d ≤ b) : IntervalIntegrable f volume c d := by
  apply IntegrableOn.intervalIntegrable
  rw [uIcc_of_le hcd]
  exact h.mono_set (Icc_subset_Icc hc hd)

/-- Découpage de l'énergie `∫ (v')²` d'une fonction de `W^{1,1}([-1,1])` d'énergie finie
sur `[-1,0]` et `[0,1]`. -/
lemma Lsq_split {v : ℝ → ℝ} (hv : IsW11 (-1) 1 v) (hE : FiniteEnergy (-1) 1 Lsq v) :
    ∃ gv : ℝ → ℝ, IntervalIntegrable gv volume (-1) 0 ∧ IntervalIntegrable gv volume 0 1 ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, v x = v (-1) + ∫ t in (-1)..x, gv t) ∧
      IntervalIntegrable (fun t => gv t ^ 2) volume (-1) 0 ∧
      IntervalIntegrable (fun t => gv t ^ 2) volume 0 1 ∧
      energy (-1) 1 Lsq v = (∫ t in (-1)..0, gv t ^ 2) + ∫ t in (0 : ℝ)..1, gv t ^ 2 ∧
      (∫ t in (-1)..0, gv t) = v 0 - v (-1) ∧ (∫ t in (0 : ℝ)..1, gv t) = v 1 - v 0 := by
  obtain ⟨gv, hg, hrep⟩ := hv
  have hae0 := W11_ae_hasDerivAt (by norm_num : (-1 : ℝ) ≤ 1) hg hrep
  have hae : ∀ c d : ℝ, -1 ≤ c → c ≤ d → d ≤ 1 →
      ∀ᵐ t, t ∈ Ι c d → deriv v t ^ 2 = gv t ^ 2 := by
    intro c d hc hcd hd
    filter_upwards [hae0, ae_ne_pt (1 : ℝ)] with t ht h1 htI
    rw [uIoc_of_le hcd] at htI
    have htI' : t ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by linarith [htI.1], lt_of_le_of_ne (htI.2.trans hd) h1⟩
    rw [(ht htI').deriv]
  have hE' : IntegrableOn (fun t => deriv v t ^ 2) (Icc (-1) 1) := hE
  have hd2 : ∀ c d : ℝ, -1 ≤ c → c ≤ d → d ≤ 1 →
      IntervalIntegrable (fun t => gv t ^ 2) volume c d := by
    intro c d hc hcd hd
    refine (intervalIntegrable_of_Icc hE' hc hcd hd).congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hae c d hc hcd hd
  have hg0 : IntervalIntegrable gv volume (-1) 0 := hg.mono_set (by
    rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc le_rfl (by norm_num))
  have hg1 : IntervalIntegrable gv volume 0 1 := hg.mono_set (by
    rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  refine ⟨gv, hg0, hg1, hrep, hd2 (-1) 0 le_rfl (by norm_num) (by norm_num),
    hd2 0 1 (by norm_num) (by norm_num) le_rfl, ?_, ?_, ?_⟩
  · rw [energy]
    simp only [energyDensity_Lsq]
    rw [intervalIntegral.integral_congr_ae (hae (-1) 1 le_rfl (by norm_num) le_rfl),
      intervalIntegral.integral_add_adjacent_intervals
        (hd2 (-1) 0 le_rfl (by norm_num) (by norm_num)) (hd2 0 1 (by norm_num) (by norm_num) le_rfl)]
  · have := hrep 0 ⟨by norm_num, by norm_num⟩
    linarith
  · have h0 := hrep 0 ⟨by norm_num, by norm_num⟩
    have h1 := hrep 1 ⟨by norm_num, by norm_num⟩
    have hadd := intervalIntegral.integral_add_adjacent_intervals hg0 hg1
    linarith

/-- L'obstacle `f(x) = -|x|`. -/
def fNegAbs : ℝ → ℝ := fun y => -|y|

lemma fNegAbs_isW11 : IsW11 (-1) 1 fNegAbs := by
  set gf : ℝ → ℝ := fun t => if t ≤ 0 then 1 else -1 with hgf
  have hgm : Measurable gf := Measurable.ite measurableSet_Iic measurable_const measurable_const
  have hgi : ∀ c d : ℝ, IntervalIntegrable gf volume c d := by
    intro c d
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
      hgm.aestronglyMeasurable (ae_of_all _ (fun t => ?_))
    simp only [hgf]
    split_ifs <;> norm_num
  refine ⟨gf, hgi (-1) 1, fun x hx => ?_⟩
  have i1 : ∀ y ∈ Icc (-1 : ℝ) 0, ∫ t in (-1)..y, gf t = y + 1 := by
    intro y hy
    have hE : EqOn gf (fun _ => (1 : ℝ)) (uIcc (-1) y) := by
      intro t ht
      rw [uIcc_of_le hy.1] at ht
      simp [hgf, ht.2.trans hy.2]
    rw [intervalIntegral.integral_congr hE, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rcases le_or_gt x 0 with h | h
  · rw [i1 x ⟨hx.1, h⟩]
    simp only [fNegAbs, abs_of_nonpos h, abs_neg, abs_one]
    ring
  · have hE : ∀ᵐ t, t ∈ Ι (0 : ℝ) x → gf t = (fun _ => (-1 : ℝ)) t := by
      refine ae_of_all _ (fun t ht => ?_)
      rw [uIoc_of_le h.le] at ht
      simp [hgf, not_le.mpr ht.1]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hgi (-1) 0) (hgi 0 x),
      i1 0 ⟨by norm_num, le_rfl⟩, intervalIntegral.integral_congr_ae hE]
    simp only [fNegAbs, abs_of_pos h, abs_neg, abs_one, intervalIntegral.integral_const,
      smul_eq_mul]
    ring

lemma fNegAbs_admissible :
    fNegAbs ∈ Admissible (-1) 1 (-1) (-1) fNegAbs (fun _ => 1) := by
  refine ⟨fNegAbs_isW11, by simp [fNegAbs], by simp [fNegAbs], fun x _ => ⟨le_rfl, ?_⟩⟩
  simp only [fNegAbs]
  linarith [abs_nonneg x]

lemma fNegAbs_deriv_sq {x : ℝ} (hx : x ≠ 0) : deriv fNegAbs x ^ 2 = 1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · have hd : HasDerivAt fNegAbs (1 * 1) x := by
      refine ((hasDerivAt_id x).const_mul 1).congr_of_eventuallyEq ?_
      filter_upwards [gt_mem_nhds h] with y hy
      simp [fNegAbs, abs_of_neg hy]
    rw [hd.deriv]
    norm_num
  · have hd : HasDerivAt fNegAbs (-1 * 1) x := by
      refine ((hasDerivAt_id x).const_mul (-1)).congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds h] with y hy
      simp [fNegAbs, abs_of_pos hy]
    rw [hd.deriv]
    norm_num

lemma fNegAbs_energy :
    FiniteEnergy (-1) 1 Lsq fNegAbs ∧ energy (-1) 1 Lsq fNegAbs = 2 := by
  have hae : ∀ᵐ t, deriv fNegAbs t ^ 2 = (1 : ℝ) := by
    filter_upwards [ae_ne_pt (0 : ℝ)] with t ht using fNegAbs_deriv_sq ht
  constructor
  · show IntegrableOn (fun t => deriv fNegAbs t ^ 2) (Icc (-1) 1)
    exact Measure.integrableOn_of_bounded (M := 1) (by simp)
      ((measurable_deriv fNegAbs).pow_const 2).aestronglyMeasurable
      (ae_restrict_of_ae (hae.mono fun t ht => by simp [ht]))
  · rw [energy]
    simp only [energyDensity_Lsq]
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (1 : ℝ)) (hae.mono (fun t ht _ => ht))]
    norm_num

/-- Pour `v` admissible d'énergie finie, `𝒥(v) ≥ 2 = 𝒥(f)`, avec égalité seulement si `v = f`
(Cauchy-Schwarz sur `[-1,0]` et `[0,1]`, et son cas d'égalité). -/
lemma fNegAbs_lower_bound {v : ℝ → ℝ}
    (hv : v ∈ Admissible (-1) 1 (-1) (-1) fNegAbs (fun _ => 1))
    (hE : FiniteEnergy (-1) 1 Lsq v) :
    2 ≤ energy (-1) 1 Lsq v ∧
      (energy (-1) 1 Lsq v ≤ 2 → ∀ x ∈ Icc (-1 : ℝ) 1, v x = fNegAbs x) := by
  obtain ⟨hW, hva, hvb, hvfg⟩ := hv
  obtain ⟨gv, hg0, hg1, hrep, hq0, hq1, hen, hs0, hs1⟩ := Lsq_split hW hE
  have hv0 : 0 ≤ v 0 := by
    have := (hvfg 0 ⟨by norm_num, by norm_num⟩).1
    simpa [fNegAbs] using this
  have cs0 := sq_integral_le (by norm_num : (-1 : ℝ) ≤ 0) hg0 hq0
  have cs1 := sq_integral_le (by norm_num : (0 : ℝ) ≤ 1) hg1 hq1
  rw [hs0, hva] at cs0
  rw [hs1, hvb] at cs1
  constructor
  · rw [hen]
    nlinarith [sq_nonneg (v 0)]
  · intro hle
    rw [hen] at hle
    have hv00 : v 0 = 0 := by nlinarith [sq_nonneg (v 0)]
    have hQ0 : ∫ t in (-1)..0, gv t ^ 2 = 1 := by
      rw [hv00] at cs0 cs1
      nlinarith
    have hQ1 : ∫ t in (0 : ℝ)..1, gv t ^ 2 = 1 := by
      rw [hv00] at cs0 cs1
      nlinarith
    -- `gv = 1` presque partout sur `]-1, 0]` et `gv = -1` presque partout sur `]0, 1]`
    have e0 : (fun t => (gv t - 1) ^ 2) = fun t => gv t ^ 2 - 2 * gv t + 1 := by
      funext t
      ring
    have e1 : (fun t => (gv t + 1) ^ 2) = fun t => gv t ^ 2 + 2 * gv t + 1 := by
      funext t
      ring
    have hi0 : IntervalIntegrable (fun t => (gv t - 1) ^ 2) volume (-1) 0 := by
      rw [e0]
      exact (hq0.sub (hg0.const_mul 2)).add intervalIntegrable_const
    have hi1 : IntervalIntegrable (fun t => (gv t + 1) ^ 2) volume 0 1 := by
      rw [e1]
      exact (hq1.add (hg1.const_mul 2)).add intervalIntegrable_const
    have z0 : ∫ t in (-1)..0, (gv t - 1) ^ 2 = 0 := by
      rw [e0, intervalIntegral.integral_add (hq0.sub (hg0.const_mul 2)) intervalIntegrable_const,
        intervalIntegral.integral_sub hq0 (hg0.const_mul 2), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul, hQ0, hs0, hva, hv00]
      norm_num
    have z1 : ∫ t in (0 : ℝ)..1, (gv t + 1) ^ 2 = 0 := by
      rw [e1, intervalIntegral.integral_add (hq1.add (hg1.const_mul 2)) intervalIntegrable_const,
        intervalIntegral.integral_add hq1 (hg1.const_mul 2), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul, hQ1, hs1, hvb, hv00]
      norm_num
    have hz0 := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun t => sq_nonneg (gv t - 1))) hi0).mp z0
    have hz1 := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun t => sq_nonneg (gv t + 1))) hi1).mp z1
    rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_Ioc.union measurableSet_Ioc)] at hz0 hz1
    have h1ae : ∀ᵐ t, t ∈ Ioc (-1 : ℝ) 0 → gv t = 1 := by
      filter_upwards [hz0] with t ht htI
      have := ht (Or.inl htI)
      simp only [Pi.zero_apply, pow_eq_zero_iff (two_ne_zero), sub_eq_zero] at this
      exact this
    have h2ae : ∀ᵐ t, t ∈ Ioc (0 : ℝ) 1 → gv t = -1 := by
      filter_upwards [hz1] with t ht htI
      have := ht (Or.inl htI)
      simp only [Pi.zero_apply, pow_eq_zero_iff (two_ne_zero)] at this
      linarith
    intro x hx
    rcases le_or_gt x 0 with h | h
    · have hI : ∫ t in (-1)..x, gv t = ∫ t in (-1)..x, (1 : ℝ) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [h1ae] with t ht htI
        rw [uIoc_of_le hx.1] at htI
        exact ht ⟨htI.1, htI.2.trans h⟩
      rw [hrep x hx, hI, hva, intervalIntegral.integral_const, smul_eq_mul]
      simp only [fNegAbs, abs_of_nonpos h]
      ring
    · have hgx : IntervalIntegrable gv volume 0 x := hg1.mono_set (by
        rw [uIcc_of_le h.le, uIcc_of_le (by norm_num)]
        exact Icc_subset_Icc le_rfl hx.2)
      have hI : ∫ t in (0 : ℝ)..x, gv t = ∫ t in (0 : ℝ)..x, (-1 : ℝ) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [h2ae] with t ht htI
        rw [uIoc_of_le h.le] at htI
        exact ht ⟨htI.1, htI.2.trans hx.2⟩
      rw [hrep x hx, ← intervalIntegral.integral_add_adjacent_intervals hg0 hgx, hs0, hI, hva,
        hv00, intervalIntegral.integral_const, smul_eq_mul]
      simp only [fNegAbs, abs_of_pos h]
      ring

lemma tendsto_of_eventually_const {F : ℝ → EReal} {c : EReal} (h : ∀ t > (0 : ℝ), F t = c) :
    liminf F (𝓝[>] 0) = c ∧ limsup F (𝓝[>] 0) = c := by
  have ht : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 c) := tendsto_const_nhds.congr' (by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t) using (h t ht).symm)
  exact ⟨ht.liminf_eq, ht.limsup_eq⟩

lemma one_not_le_neg_one : ¬ ((1 : EReal) ≤ -1) := by
  intro h
  have h' : ((1 : ℝ) : EReal) ≤ ((-1 : ℝ) : EReal) := by simpa using h
  have := EReal.coe_le_coe_iff.mp h'
  norm_num at this

/-- **Remarque 2.6(b), obstacle inférieur.** Pour `L(x,w,v) = v²` sur `[-1,1]`, `f(x) = -|x|`,
`g ≡ 1` et `A = B = -1` : `L` vérifie (H₁) et (H₂), `f` est l'unique solution, `f` a un
« coin concave » en `0` (`D₋f(0) = 1 > -1 = D⁺f(0)`, donc (O_f) échoue) et la solution n'a
pas la régularité partielle de Tonelli. -/
theorem remark_2_6b_lower :
    ContinuousOn fNegAbs (Icc (-1) 1) ∧ (∀ x ∈ Icc (-1 : ℝ) 1, fNegAbs x < 1) ∧
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Lsq p.1 p.2.1 p.2.2)
      (Icc (-1) 1 ×ˢ (univ : Set (ℝ × ℝ))) ∧
    HypH1 (-1) 1 Lsq ∧ HypH2 (-1) 1 Lsq ∧
    IsSolution (-1) 1 (-1) (-1) Lsq fNegAbs (fun _ => 1) fNegAbs ∧
    (∀ u, IsSolution (-1) 1 (-1) (-1) Lsq fNegAbs (fun _ => 1) u →
      ∀ x ∈ Icc (-1 : ℝ) 1, u x = fNegAbs x) ∧
    dLowerLeft fNegAbs 0 = 1 ∧ dUpperRight fNegAbs 0 = -1 ∧
    ¬ (dLowerLeft fNegAbs 0 ≤ dUpperRight fNegAbs 0) ∧
    ¬ TonelliRegular (-1) 1 fNegAbs := by
  obtain ⟨hfE, hf2⟩ := fNegAbs_energy
  have hEf : energyE (-1) 1 Lsq fNegAbs = ((2 : ℝ) : EReal) := by
    rw [energyE_of_finite hfE, hf2]
  have hdL : dLowerLeft fNegAbs 0 = 1 := by
    refine (tendsto_of_eventually_const (fun t ht => ?_)).1
    simp [eslope, slope_def_field, fNegAbs, abs_of_pos ht, ht.ne']
  have hdR : dUpperRight fNegAbs 0 = -1 := by
    refine (tendsto_of_eventually_const (fun t ht => ?_)).2
    simp [eslope, slope_def_field, fNegAbs, abs_of_pos ht, ht.ne']
  have hO : ¬ (dLowerLeft fNegAbs 0 ≤ dUpperRight fNegAbs 0) := by
    rw [hdL, hdR]
    exact one_not_le_neg_one
  refine ⟨?_, fun x _ => ?_, Lsq_continuousOn _ _, Lsq_H1 _ _, Lsq_H2 _ _,
    ⟨fNegAbs_admissible, fun v hv => ?_⟩, fun u hu => ?_, hdL, hdR, hO, ?_⟩
  · unfold fNegAbs
    exact Continuous.continuousOn (by fun_prop)
  · simp only [fNegAbs]
    linarith [abs_nonneg x]
  · rw [hEf]
    by_cases hE : FiniteEnergy (-1) 1 Lsq v
    · rw [energyE_of_finite hE]
      exact EReal.coe_le_coe_iff.mpr (fNegAbs_lower_bound hv hE).1
    · rw [energyE_of_not_finite hE]
      exact le_top
  · have h := hu.2 fNegAbs fNegAbs_admissible
    rw [hEf] at h
    by_cases hE : FiniteEnergy (-1) 1 Lsq u
    · rw [energyE_of_finite hE] at h
      exact (fNegAbs_lower_bound hu.1 hE).2 (EReal.coe_le_coe_iff.mp h)
    · rw [energyE_of_not_finite hE] at h
      exact absurd ((EReal.coe_lt_top 2).trans_le h) (lt_irrefl _)
  · intro hT
    obtain ⟨p, hp⟩ := tendsto_slope_of_tonelli hT 0 ⟨by norm_num, by norm_num⟩
    obtain ⟨h1, -, -, h4⟩ := dini_of_tendsto hp
    exact hO (le_of_eq (h4.trans h1.symm))

/-! ### L'obstacle supérieur, par symétrie `u ↦ -u` -/

/-- L'obstacle `g(x) = |x|`. -/
def gAbs : ℝ → ℝ := fun y => |y|

lemma isW11_neg {a b : ℝ} {v : ℝ → ℝ} (hv : IsW11 a b v) : IsW11 a b (fun y => -v y) := by
  obtain ⟨g, hg, hrep⟩ := hv
  refine ⟨fun t => -g t, hg.neg, fun x hx => ?_⟩
  rw [intervalIntegral.integral_neg]
  simp only [hrep x hx]
  ring

lemma energyDensity_Lsq_neg (v : ℝ → ℝ) :
    energyDensity Lsq (fun y => -v y) = energyDensity Lsq v := by
  funext x
  simp only [energyDensity_Lsq, deriv.fun_neg, neg_sq]

lemma energyE_Lsq_neg (a b : ℝ) (v : ℝ → ℝ) :
    energyE a b Lsq (fun y => -v y) = energyE a b Lsq v := by
  have h := energyDensity_Lsq_neg v
  unfold energyE FiniteEnergy energy
  rw [h]

lemma adm_neg₁ {v : ℝ → ℝ} (hv : v ∈ Admissible (-1) 1 1 1 (fun _ => -1) gAbs) :
    (fun y => -v y) ∈ Admissible (-1) 1 (-1) (-1) fNegAbs (fun _ => 1) := by
  obtain ⟨hW, ha, hb, h⟩ := hv
  refine ⟨isW11_neg hW, by simp [ha], by simp [hb], fun x hx => ?_⟩
  have := h x hx
  simp only [fNegAbs, gAbs] at this ⊢
  constructor <;> linarith [this.1, this.2]

lemma adm_neg₂ {w : ℝ → ℝ} (hw : w ∈ Admissible (-1) 1 (-1) (-1) fNegAbs (fun _ => 1)) :
    (fun y => -w y) ∈ Admissible (-1) 1 1 1 (fun _ => -1) gAbs := by
  obtain ⟨hW, ha, hb, h⟩ := hw
  refine ⟨isW11_neg hW, by simp [ha], by simp [hb], fun x hx => ?_⟩
  have := h x hx
  simp only [fNegAbs, gAbs] at this ⊢
  constructor <;> linarith [this.1, this.2]

lemma gAbs_eq_neg : gAbs = fun y => -fNegAbs y := by
  funext y
  simp [gAbs, fNegAbs]

/-- **Remarque 2.6(b), obstacle supérieur.** Pour `L(x,w,v) = v²` sur `[-1,1]`, `f ≡ -1`,
`g(x) = |x|` et `A = B = 1` : `g` est l'unique solution, `g` a un « coin convexe » en `0`
(`D₊g(0) = 1 > -1 = D⁻g(0)`, donc (O_g) échoue) et la solution n'a pas la régularité
partielle de Tonelli. -/
theorem remark_2_6b_upper :
    ContinuousOn gAbs (Icc (-1) 1) ∧ (∀ x ∈ Icc (-1 : ℝ) 1, -1 < gAbs x) ∧
    IsSolution (-1) 1 1 1 Lsq (fun _ => -1) gAbs gAbs ∧
    (∀ u, IsSolution (-1) 1 1 1 Lsq (fun _ => -1) gAbs u →
      ∀ x ∈ Icc (-1 : ℝ) 1, u x = gAbs x) ∧
    dLowerRight gAbs 0 = 1 ∧ dUpperLeft gAbs 0 = -1 ∧
    ¬ (dLowerRight gAbs 0 ≤ dUpperLeft gAbs 0) ∧
    ¬ TonelliRegular (-1) 1 gAbs := by
  obtain ⟨-, -, -, -, -, hsol, huniq, -⟩ := remark_2_6b_lower
  have hdR : dLowerRight gAbs 0 = 1 := by
    refine (tendsto_of_eventually_const (fun t ht => ?_)).1
    simp [eslope, slope_def_field, gAbs, abs_of_pos ht, ht.ne']
  have hdL : dUpperLeft gAbs 0 = -1 := by
    refine (tendsto_of_eventually_const (fun t ht => ?_)).2
    simp [eslope, slope_def_field, gAbs, abs_of_pos ht, ht.ne']
  have hO : ¬ (dLowerRight gAbs 0 ≤ dUpperLeft gAbs 0) := by
    rw [hdR, hdL]
    exact one_not_le_neg_one
  have hgA : gAbs ∈ Admissible (-1) 1 1 1 (fun _ => -1) gAbs := by
    have h := adm_neg₂ fNegAbs_admissible
    rwa [← gAbs_eq_neg] at h
  refine ⟨?_, fun x _ => ?_, ⟨hgA, fun v hv => ?_⟩, fun u hu => ?_, hdR, hdL, hO, ?_⟩
  · unfold gAbs
    exact Continuous.continuousOn (by fun_prop)
  · simp only [gAbs]
    linarith [abs_nonneg x]
  · have h := hsol.2 _ (adm_neg₁ hv)
    rw [energyE_Lsq_neg] at h
    rw [gAbs_eq_neg, energyE_Lsq_neg]
    exact h
  · have hu' : IsSolution (-1) 1 (-1) (-1) Lsq fNegAbs (fun _ => 1) (fun y => -u y) := by
      refine ⟨adm_neg₁ hu.1, fun w hw => ?_⟩
      have h := hu.2 _ (adm_neg₂ hw)
      rw [energyE_Lsq_neg] at h
      rw [energyE_Lsq_neg]
      exact h
    intro x hx
    have := huniq _ hu' x hx
    simp only [fNegAbs, gAbs] at this ⊢
    linarith
  · intro hT
    obtain ⟨p, hp⟩ := tendsto_slope_of_tonelli hT 0 ⟨by norm_num, by norm_num⟩
    obtain ⟨-, h2, h3, -⟩ := dini_of_tendsto hp
    exact hO (le_of_eq (h2.trans h3.symm))

/-! ## Remarque 2.6(c) : l'hypothèse d'énergie finie ne peut pas être supprimée -/

/-- L'obstacle `f(x) = (x - a)^{1/3}`. -/
def fCube (a : ℝ) : ℝ → ℝ := fun x => (x - a) ^ ((1 : ℝ) / 3)

/-- La dérivée de `f` en `x > a`. -/
def dCube (a : ℝ) : ℝ → ℝ := fun x => 1 * ((1 : ℝ) / 3) * (x - a) ^ ((1 : ℝ) / 3 - 1)

lemma fCube_continuous (a : ℝ) : Continuous (fCube a) :=
  (continuous_id.sub continuous_const).rpow_const (fun _ => Or.inr (by norm_num))

lemma fCube_a (a : ℝ) : fCube a a = 0 := by
  simp [fCube]

lemma fCube_hasDerivAt {a x : ℝ} (hx : a < x) : HasDerivAt (fCube a) (dCube a x) x :=
  ((hasDerivAt_id' x).sub_const a).rpow_const (Or.inl (sub_ne_zero.mpr hx.ne'))

lemma dCube_continuousAt {a x : ℝ} (hx : a < x) : ContinuousAt (dCube a) x :=
  continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).rpow_const
    (Or.inl (sub_ne_zero.mpr hx.ne')))

lemma tendsto_sub_nhdsGT (a : ℝ) : Tendsto (fun t => t - a) (𝓝[>] a) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun t => t - a) (𝓝 a) (𝓝 (a - a)) :=
      (continuous_id.sub continuous_const).tendsto a
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t (ht : a < t)
    exact sub_pos.mpr ht

lemma rpow_tendsto_atTop (a : ℝ) :
    Tendsto (fun t => (t - a) ^ ((1 : ℝ) / 3 - 1)) (𝓝[>] a) atTop :=
  (tendsto_rpow_neg_nhdsGT_zero (by norm_num : (1 : ℝ) / 3 - 1 < 0)).comp (tendsto_sub_nhdsGT a)

lemma dCube_tendsto_atTop (a : ℝ) : Tendsto (dCube a) (𝓝[>] a) atTop :=
  (rpow_tendsto_atTop a).const_mul_atTop (by norm_num)

lemma fCube_slope {a t : ℝ} (ht : a < t) :
    slope (fCube a) a t = (t - a) ^ ((1 : ℝ) / 3 - 1) := by
  rw [slope_def_field, Real.rpow_sub_one (sub_ne_zero.mpr ht.ne'), fCube_a, sub_zero]
  rfl

lemma fCube_isW11 {a b : ℝ} (_hab : a < b) : IsW11 a b (fCube a) := by
  have hint : ∀ x, IntervalIntegrable (dCube a) volume a x := by
    intro x
    have h1 := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := x - a)
      (by norm_num : -1 < (1 : ℝ) / 3 - 1)).comp_sub_right a
    simp only [zero_add, sub_add_cancel] at h1
    exact h1.const_mul (1 * ((1 : ℝ) / 3))
  refine ⟨dCube a, hint b, fun x hx => ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx.1
    (fCube_continuous a).continuousOn
    (fun t ht => (fCube_hasDerivAt ht.1).hasDerivWithinAt) (hint x)]
  ring

/-- La dérivée de Tonelli de `f` : `+∞` en `a`, `f'(x)` ailleurs. -/
def dCubeE (a : ℝ) (x : ℝ) : EReal := if x = a then ⊤ else ((dCube a x : ℝ) : EReal)

lemma fCube_hasEDeriv_a {a b : ℝ} : HasEDerivWithinIcc a b (fCube a) ⊤ a := by
  unfold HasEDerivWithinIcc
  rw [EReal.tendsto_nhds_top_iff_real]
  intro y
  have hreal := tendsto_atTop.mp (rpow_tendsto_atTop a) (y + 1)
  have hmono : 𝓝[Icc a b \ {a}] a ≤ 𝓝[>] a :=
    nhdsWithin_mono _ (fun t ht => lt_of_le_of_ne ht.1.1 (Ne.symm ht.2))
  filter_upwards [hmono hreal, hmono self_mem_nhdsWithin] with t ht (hat : a < t)
  rw [eslope, fCube_slope hat]
  exact EReal.coe_lt_coe_iff.mpr (by linarith)

lemma dCubeE_tendsto_top {a b : ℝ} : Tendsto (dCubeE a) (𝓝[Icc a b] a) (𝓝 ⊤) := by
  rw [EReal.tendsto_nhds_top_iff_real]
  intro y
  have h := tendsto_atTop.mp (dCube_tendsto_atTop a) (y + 1)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hu)]
    with t htI htu
  by_cases hta : t = a
  · simp [dCubeE, hta]
  · have htIoo : t ∈ Ioo a u := ⟨lt_of_le_of_ne htI.1 (Ne.symm hta), htu⟩
    have := hsub htIoo
    simp only [dCubeE, if_neg hta]
    exact EReal.coe_lt_coe_iff.mpr (by simp only [mem_ofPred_eq] at this; linarith)

/-- `f(x) = (x - a)^{1/3}` a la régularité partielle de Tonelli, avec `f'(a) = +∞`. -/
lemma fCube_tonelli {a b : ℝ} (hab : a < b) : TonelliRegular a b (fCube a) := by
  refine ⟨fCube_isW11 hab, dCubeE a, ⟨fun x hx => ?_, fun x hx => ?_, ?_⟩⟩
  · by_cases hxa : x = a
    · rw [hxa]
      simpa [dCubeE] using (fCube_hasEDeriv_a (b := b))
    · have hxa' : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
      simp only [dCubeE, if_neg hxa]
      have h := EReal.tendsto_coe.mpr (hasDerivAt_iff_tendsto_slope.mp (fCube_hasDerivAt hxa'))
      exact h.mono_left (nhdsWithin_mono _ (fun y hy => hy.2))
  · by_cases hxa : x = a
    · rw [hxa]
      show Tendsto (dCubeE a) (𝓝[Icc a b] a) (𝓝 (dCubeE a a))
      simpa [dCubeE] using (dCubeE_tendsto_top (a := a) (b := b))
    · have hxa' : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
      have hc : ContinuousAt (fun t => ((dCube a t : ℝ) : EReal)) x :=
        continuous_coe_real_ereal.continuousAt.comp (dCube_continuousAt hxa')
      refine (hc.congr_of_eventuallyEq ?_).continuousWithinAt
      filter_upwards [eventually_ne_nhds hxa] with t ht
      simp [dCubeE, ht]
  · refine measure_mono_null (fun t ht => ?_) (measure_singleton a)
    by_contra hta
    have hta' : t ≠ a := fun h => hta (by simp [h])
    obtain ⟨-, h⟩ := ht
    simp only [dCubeE, if_neg hta'] at h
    rcases h with h | h
    · exact EReal.coe_ne_top _ h
    · exact EReal.coe_ne_bot _ h

/-- La régularité de Tonelli est préservée par l'ajout d'une constante. -/
lemma tonelli_add_const {a b C : ℝ} {u : ℝ → ℝ} (hu : TonelliRegular a b u) :
    TonelliRegular a b (fun x => u x + C) := by
  obtain ⟨⟨g, hg, hrep⟩, u', hder, hcont, hvol⟩ := hu
  have hs : ∀ s t, eslope (fun x => u x + C) s t = eslope u s t := by
    intro s t
    show ((slope (fun x => u x + C) s t : ℝ) : EReal) = ((slope u s t : ℝ) : EReal)
    congr 1
    simp only [slope_def_field]
    ring
  refine ⟨⟨g, hg, fun x hx => ?_⟩, u', fun x hx => ?_, hcont, hvol⟩
  · simp only [hrep x hx]
    ring
  · have := hder x hx
    unfold HasEDerivWithinIcc at this ⊢
    simpa only [hs] using this

/-- Tout `v` admissible est d'énergie infinie : sinon `v` serait `½`-höldérienne
(Lemme 3.1), alors que `v ≥ f` et `v(a) = f(a)` imposent `(y - a)^{1/3} ≤ N √(y - a)`. -/
lemma fCube_not_finiteEnergy {a b : ℝ} (hab : a < b) {L : ℝ → ℝ → ℝ → ℝ}
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH2 : HypH2 a b L) {v : ℝ → ℝ}
    (hv : v ∈ Admissible a b 0 (fCube a b) (fCube a) (fun x => fCube a x + 1)) :
    ¬ FiniteEnergy a b L v := by
  intro hE
  obtain ⟨hW, hva, -, hvfg⟩ := hv
  obtain ⟨-, N, hN0, hN⟩ := holder_half hab.le hL hH2 hW hE
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min (1 / (N + 2)) (min 1 (b - a)) := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [ht]
    exact lt_min (by positivity) (lt_min one_pos (by linarith))
  have ht1 : t ≤ 1 := by rw [ht]; exact (min_le_right _ _).trans (min_le_left _ _)
  have htb : t ≤ b - a := by rw [ht]; exact (min_le_right _ _).trans (min_le_right _ _)
  have htN : t ≤ 1 / (N + 2) := by rw [ht]; exact min_le_left _ _
  have ht6 : t ^ 6 ≤ t := pow_le_of_le_one ht0.le ht1 (by norm_num)
  have hyI : a + t ^ 6 ∈ Icc a b := ⟨by have := pow_pos ht0 6; linarith, by linarith⟩
  have haI : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have h1 := hN a haI (a + t ^ 6) hyI hyI.1
  have h2 := (hvfg (a + t ^ 6) hyI).1
  have hfy : fCube a (a + t ^ 6) = t ^ 2 := by
    simp only [fCube, add_sub_cancel_left]
    rw [show t ^ 6 = t ^ (6 : ℝ) by norm_cast, ← Real.rpow_mul ht0.le,
      show (6 : ℝ) * (1 / 3) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hsq : Real.sqrt (a + t ^ 6 - a) = t ^ 3 := by
    rw [add_sub_cancel_left, show t ^ 6 = (t ^ 3) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq, hva] at h1
  rw [hfy] at h2
  have h3 : t ^ 2 ≤ N * t ^ 3 := by
    have := le_abs_self (v (a + t ^ 6) - 0)
    linarith
  have h4 : N * t < 1 := by
    have h5 : N * t ≤ N * (1 / (N + 2)) := mul_le_mul_of_nonneg_left htN hN0
    have h6 : N * (1 / (N + 2)) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    linarith
  have h5 : t ^ 2 * (N * t) < t ^ 2 * 1 := mul_lt_mul_of_pos_left h4 (by positivity)
  nlinarith

/-- Toute fonction admissible est solution (elles sont toutes d'énergie infinie). -/
lemma fCube_isSolution {a b : ℝ} (hab : a < b) {L : ℝ → ℝ → ℝ → ℝ}
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH2 : HypH2 a b L) {v : ℝ → ℝ}
    (hv : v ∈ Admissible a b 0 (fCube a b) (fCube a) (fun x => fCube a x + 1)) :
    IsSolution a b 0 (fCube a b) L (fCube a) (fun x => fCube a x + 1) v :=
  ⟨hv, fun w hw => le_of_eq (by
    rw [energyE_of_not_finite (fCube_not_finiteEnergy hab hL hH2 hv),
      energyE_of_not_finite (fCube_not_finiteEnergy hab hL hH2 hw)])⟩

/-! ### La solution oscillante `v = f + λ w`, `w(x) = φ(x) (x - c)² (2 + sin(1/(x - c)))` -/

/-- `h(x) = (x - c)² (2 + sin(1/(x - c)))` ; en `c`, elle vaut `0` (convention `1/0 = 0`). -/
def hOsc (c : ℝ) : ℝ → ℝ := fun x => (x - c) ^ 2 * (2 + Real.sin (1 / (x - c)))

/-- La dérivée de `h` hors de `c`. -/
def dOsc (c : ℝ) : ℝ → ℝ := fun x =>
  2 * (x - c) * (2 + Real.sin (1 / (x - c))) - Real.cos (1 / (x - c))

/-- La dérivée de `h`, qui vaut `0` en `c`. -/
def dOsc' (c : ℝ) (x : ℝ) : ℝ := if x = c then 0 else dOsc c x

/-- `w = φ h`. -/
def wOsc (c : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun x => φ x * hOsc c x

/-- La solution `v = f + λ w`. -/
def vOsc (a c lam : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun x => fCube a x + lam * wOsc c φ x

lemma hOsc_c (c : ℝ) : hOsc c c = 0 := by simp [hOsc]

lemma hOsc_bounds (c x : ℝ) : 0 ≤ hOsc c x ∧ hOsc c x ≤ 3 * (x - c) ^ 2 := by
  have h1 := Real.neg_one_le_sin (1 / (x - c))
  have h2 := Real.sin_le_one (1 / (x - c))
  simp only [hOsc]
  constructor <;> nlinarith [sq_nonneg (x - c)]

lemma hOsc_hasDerivAt_ne {c x : ℝ} (hx : x ≠ c) : HasDerivAt (hOsc c) (dOsc c x) x := by
  have hxc : x - c ≠ 0 := sub_ne_zero.mpr hx
  have h1 : HasDerivAt (fun y => y - c) 1 x := (hasDerivAt_id' x).sub_const c
  have h2 : HasDerivAt (fun y => (y - c) ^ 2) (2 * (x - c)) x := by
    simpa using h1.fun_pow 2
  have h3 : HasDerivAt (fun y => 1 / (y - c)) (-1 / (x - c) ^ 2) x := by
    simpa [one_div] using h1.fun_inv hxc
  have h5 := h2.fun_mul (h3.sin.const_add 2)
  have key : dOsc c x = 2 * (x - c) * (2 + Real.sin (1 / (x - c))) +
      (x - c) ^ 2 * (Real.cos (1 / (x - c)) * (-1 / (x - c) ^ 2)) := by
    simp only [dOsc]
    field_simp
    ring
  rw [key]
  exact h5

lemma hOsc_hasDerivAt_c (c : ℝ) : HasDerivAt (hOsc c) 0 c := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hc : Continuous (fun x : ℝ => 3 * |x - c|) := by fun_prop
  have hlim := hc.tendsto c
  simp only [sub_self, abs_zero, mul_zero] at hlim
  refine squeeze_zero_norm' ?_ (hlim.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with x (hx : x ≠ c)
  have hxc : x - c ≠ 0 := sub_ne_zero.mpr hx
  have h1 := Real.neg_one_le_sin (1 / (x - c))
  have h2 := Real.sin_le_one (1 / (x - c))
  have h3 : |2 + Real.sin (1 / (x - c))| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [slope_def_field, hOsc_c, sub_zero, Real.norm_eq_abs]
  simp only [hOsc]
  rw [pow_two, mul_assoc, mul_div_cancel_left₀ _ hxc, abs_mul]
  nlinarith [abs_nonneg (x - c), abs_nonneg (2 + Real.sin (1 / (x - c)))]

lemma hOsc_hasDerivAt (c x : ℝ) : HasDerivAt (hOsc c) (dOsc' c x) x := by
  by_cases hx : x = c
  · rw [dOsc', if_pos hx, hx]
    exact hOsc_hasDerivAt_c c
  · rw [dOsc', if_neg hx]
    exact hOsc_hasDerivAt_ne hx

lemma dOsc'_bound (c x : ℝ) : |dOsc' c x| ≤ 6 * |x - c| + 1 := by
  unfold dOsc'
  split_ifs with hx
  · rw [abs_zero]
    positivity
  · have h1 := Real.neg_one_le_sin (1 / (x - c))
    have h2 := Real.sin_le_one (1 / (x - c))
    have h3 := Real.neg_one_le_cos (1 / (x - c))
    have h4 := Real.cos_le_one (1 / (x - c))
    simp only [dOsc]
    rw [abs_le]
    rcases le_total 0 (x - c) with h | h
    · rw [abs_of_nonneg h]
      constructor <;> nlinarith
    · rw [abs_of_nonpos h]
      constructor <;> nlinarith

lemma isW11_of_differentiable_bounded {a b M : ℝ} (hab : a ≤ b) {w : ℝ → ℝ}
    (hd : ∀ x, DifferentiableAt ℝ w x) (hM : ∀ x ∈ Icc a b, |deriv w x| ≤ M) :
    IsW11 a b w := by
  have hint : ∀ x ∈ Icc a b, IntervalIntegrable (deriv w) volume a x := by
    intro x hx
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
      (measurable_deriv w).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine ae_of_all _ (fun t ht => ?_)
    rw [uIoc_of_le hx.1] at ht
    rw [Real.norm_eq_abs]
    exact hM t ⟨ht.1.le, ht.2.trans hx.2⟩
  refine ⟨deriv w, hint b ⟨hab, le_rfl⟩, fun x hx => ?_⟩
  rw [intervalIntegral.integral_deriv_eq_sub (fun t _ => hd t) (hint x hx)]
  ring

lemma isW11_add' {a b : ℝ} (hab : a ≤ b) {u v : ℝ → ℝ} (hu : IsW11 a b u) (hv : IsW11 a b v) :
    IsW11 a b (fun x => u x + v x) := by
  obtain ⟨g, hg, hrep⟩ := hu
  obtain ⟨k, hk, hrep'⟩ := hv
  refine ⟨fun t => g t + k t, hg.add hk, fun x hx => ?_⟩
  have hsub : uIcc a x ⊆ uIcc a b := by
    rw [uIcc_of_le hx.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hx.2
  rw [intervalIntegral.integral_add (hg.mono_set hsub) (hk.mono_set hsub)]
  simp only [hrep x hx, hrep' x hx]
  ring

lemma isW11_const_mul {a b : ℝ} (C : ℝ) {u : ℝ → ℝ} (hu : IsW11 a b u) :
    IsW11 a b (fun x => C * u x) := by
  obtain ⟨g, hg, hrep⟩ := hu
  refine ⟨fun t => C * g t, hg.const_mul C, fun x hx => ?_⟩
  rw [intervalIntegral.integral_const_mul]
  simp only [hrep x hx]
  ring

lemma wOsc_hasDerivAt {c : ℝ} {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (x : ℝ) :
    HasDerivAt (wOsc c φ) (deriv φ x * hOsc c x + φ x * dOsc' c x) x :=
  ((hφ.differentiable (by norm_num)) x).hasDerivAt.fun_mul (hOsc_hasDerivAt c x)

lemma wOsc_isW11 {a b c : ℝ} (hab : a ≤ b) (hc : c ∈ Icc a b) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφ1 : ∀ x, |φ x| ≤ 1) : IsW11 a b (wOsc c φ) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b)
    (hφ.continuous_deriv le_rfl).continuousOn
  refine isW11_of_differentiable_bounded hab (fun x => (wOsc_hasDerivAt hφ x).differentiableAt)
    (M := K * (3 * (b - a) ^ 2) + 1 * (6 * (b - a) + 1)) (fun x hx => ?_)
  rw [(wOsc_hasDerivAt hφ x).deriv]
  have hxc : |x - c| ≤ b - a :=
    abs_le.mpr ⟨by linarith [hx.1, hc.2], by linarith [hx.2, hc.1]⟩
  have hK' : |deriv φ x| ≤ K := by simpa using hK x hx
  have hb := hOsc_bounds c x
  have hd := dOsc'_bound c x
  have hh : |hOsc c x| ≤ 3 * (b - a) ^ 2 := by
    rw [abs_of_nonneg hb.1]
    have : (x - c) ^ 2 ≤ (b - a) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hxc 2
    linarith [hb.2]
  have hK0 : 0 ≤ K := (abs_nonneg _).trans hK'
  have e1 : |deriv φ x| * |hOsc c x| ≤ K * (3 * (b - a) ^ 2) :=
    mul_le_mul hK' hh (abs_nonneg _) hK0
  have e2 : |φ x| * |dOsc' c x| ≤ 1 * (6 * (b - a) + 1) :=
    mul_le_mul (hφ1 x) (by linarith [hd, hxc]) (abs_nonneg _) zero_le_one
  have e3 := abs_add_le (deriv φ x * hOsc c x) (φ x * dOsc' c x)
  rw [abs_mul, abs_mul] at e3
  linarith

/-- `v = f + λ w` est admissible (donc solution) dès que `0 ≤ λ w < 1` sur `[a,b]`. -/
lemma vOsc_admissible {a b c lam : ℝ} (hab : a < b) (hc : c ∈ Ioo a b) (hlam : 0 < lam)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφa : φ a = 0) (hφb : φ b = 0)
    (hφ01 : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) (hsmall : ∀ x ∈ Icc a b, lam * wOsc c φ x < 1) :
    vOsc a c lam φ ∈ Admissible a b 0 (fCube a b) (fCube a) (fun x => fCube a x + 1) := by
  have hφ1 : ∀ x, |φ x| ≤ 1 := fun x => abs_le.mpr ⟨by linarith [(hφ01 x).1], (hφ01 x).2⟩
  refine ⟨isW11_add' hab.le (fCube_isW11 hab)
    (isW11_const_mul lam (wOsc_isW11 hab.le (Ioo_subset_Icc_self hc) hφ hφ1)), ?_, ?_,
    fun x hx => ⟨?_, ?_⟩⟩
  · simp [vOsc, wOsc, hφa, fCube_a]
  · simp [vOsc, wOsc, hφb]
  · have : 0 ≤ lam * wOsc c φ x :=
      mul_nonneg hlam.le (mul_nonneg (hφ01 x).1 (hOsc_bounds c x).1)
    simp only [vOsc]
    linarith
  · have := hsmall x hx
    simp only [vOsc]
    linarith

/-- `v = f + λ w` n'a pas la régularité partielle de Tonelli : près de `c`,
`v' = f' + λ (2 (x - c)(2 + sin(1/(x - c))) - cos(1/(x - c)))` n'est pas continue en `c`. -/
lemma vOsc_not_tonelli {a b c lam : ℝ} (hc : c ∈ Ioo a b) (hlam : 0 < lam)
    {φ : ℝ → ℝ} (hφc : ∀ᶠ x in 𝓝 c, φ x = 1) :
    ¬ TonelliRegular a b (vOsc a c lam φ) := by
  rintro ⟨-, u', hder, hcont, -⟩
  have hlam0 : lam ≠ 0 := hlam.ne'
  -- une boule `|x - c| < r` où `φ = 1`, contenue dans `]a,b[`
  obtain ⟨ε, hε, hεφ⟩ := Metric.eventually_nhds_iff.mp hφc
  obtain ⟨r, hr⟩ : ∃ r, r = min ε (min (c - a) (b - c)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    rw [hr]
    exact lt_min hε (lt_min (by linarith [hc.1]) (by linarith [hc.2]))
  have hball : ∀ x, |x - c| < r → x ∈ Ioo a b ∧ φ x = 1 := by
    intro x hx
    have h1 : r ≤ ε := by rw [hr]; exact min_le_left _ _
    have h2 : r ≤ c - a := by rw [hr]; exact (min_le_right _ _).trans (min_le_left _ _)
    have h3 : r ≤ b - c := by rw [hr]; exact (min_le_right _ _).trans (min_le_right _ _)
    have := abs_lt.mp hx
    refine ⟨⟨by linarith, by linarith⟩, hεφ ?_⟩
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hopen : IsOpen {y : ℝ | |y - c| < r} := isOpen_lt (by fun_prop) continuous_const
  have hc0 : |c - c| < r := by simp [hr0]
  -- la dérivée de `v` dans la boule
  set Dv : ℝ → ℝ := fun x => dCube a x + lam * dOsc' c x with hDv
  have hvd : ∀ x, |x - c| < r → HasDerivAt (vOsc a c lam φ) (Dv x) x := by
    intro x hx
    have hxI := (hball x hx).1
    have hd : HasDerivAt (fun y => fCube a y + lam * hOsc c y) (Dv x) x :=
      (fCube_hasDerivAt hxI.1).fun_add ((hOsc_hasDerivAt c x).const_mul lam)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hx] with y hy
    simp only [vOsc, wOsc, (hball y hy).2, one_mul]
  have hu' : ∀ x, |x - c| < r → u' x = ((Dv x : ℝ) : EReal) := fun x hx =>
    eDeriv_eq_of_hasDerivAt (hball x hx).1 (hder x (Ioo_subset_Icc_self (hball x hx).1))
      (hvd x hx)
  -- la continuité de `u'` en `c` force celle de `v'`
  have hca : ContinuousAt u' c :=
    (hcont c (Ioo_subset_Icc_self hc)).continuousAt (Icc_mem_nhds hc.1 hc.2)
  have hDvt : Tendsto Dv (𝓝 c) (𝓝 (Dv c)) := by
    have heq : u' =ᶠ[𝓝 c] fun x => ((Dv x : ℝ) : EReal) := by
      filter_upwards [hopen.mem_nhds hc0] with x hx using hu' x hx
    have h1 : Tendsto (fun x => ((Dv x : ℝ) : EReal)) (𝓝 c) (𝓝 (u' c)) :=
      Tendsto.congr' heq hca
    rw [hu' c hc0] at h1
    exact EReal.tendsto_coe.mp h1
  -- donc `cos(1/(x - c)) → 0` quand `x → c`, `x ≠ c`
  have hT1 : Tendsto (fun x => 2 * (x - c) * (2 + Real.sin (1 / (x - c)))) (𝓝[≠] c) (𝓝 0) := by
    have hc6 : Continuous (fun x : ℝ => 6 * |x - c|) := by fun_prop
    have hlim := hc6.tendsto c
    simp only [sub_self, abs_zero, mul_zero] at hlim
    refine squeeze_zero_norm' (Filter.Eventually.of_forall (fun x => ?_))
      (hlim.mono_left nhdsWithin_le_nhds)
    have h1 := Real.neg_one_le_sin (1 / (x - c))
    have h2 := Real.sin_le_one (1 / (x - c))
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two,
      abs_of_pos (by linarith : (0 : ℝ) < 2 + Real.sin (1 / (x - c)))]
    nlinarith [abs_nonneg (x - c)]
  have hdc : Tendsto (dCube a) (𝓝 c) (𝓝 (dCube a c)) := dCube_continuousAt hc.1
  have hT2 : Tendsto (fun x => (Dv x - dCube a x) / lam) (𝓝[≠] c) (𝓝 0) := by
    have h := ((hDvt.sub hdc).div_const lam).mono_left (nhdsWithin_le_nhds (s := {c}ᶜ))
    have h0 : (Dv c - dCube a c) / lam = 0 := by simp [hDv, dOsc']
    rwa [h0] at h
  have hcos : Tendsto (fun x => Real.cos (1 / (x - c))) (𝓝[≠] c) (𝓝 0) := by
    have h := hT1.sub hT2
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : x ≠ c)
    simp only [hDv, dOsc', if_neg hx, dOsc]
    field_simp
    ring
  -- mais `cos(1/(x_n - c)) = 1` pour `x_n = c + 1/(2π(n+1))`
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  set xs : ℕ → ℝ := fun n => c + 1 / (2 * Real.pi) * (1 / ((n : ℝ) + 1)) with hxs
  have hxs_ne : ∀ n, xs n ≠ c := by
    intro n h
    have hpos : 0 < 1 / (2 * Real.pi) * (1 / ((n : ℝ) + 1)) := by positivity
    simp only [hxs] at h
    linarith
  have hxs_t : Tendsto xs atTop (𝓝[≠] c) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall hxs_ne⟩
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / (2 * Real.pi))).const_add c
    simpa [hxs] using h
  have hcos1 : ∀ n, Real.cos (1 / (xs n - c)) = 1 := by
    intro n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have e : 1 / (xs n - c) = ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
      simp only [hxs, add_sub_cancel_left]
      push_cast
      field_simp
    rw [e, Real.cos_nat_mul_two_pi]
  have hlim : Tendsto (fun n => Real.cos (1 / (xs n - c))) atTop (𝓝 0) := hcos.comp hxs_t
  have hconst : (fun n => Real.cos (1 / (xs n - c))) = fun _ => (1 : ℝ) := funext hcos1
  rw [hconst] at hlim
  have := tendsto_nhds_unique hlim tendsto_const_nhds
  norm_num at this

/-- Il existe une fonction plateau `φ` lisse, `0 ≤ φ ≤ 1`, nulle en `a` et `b`, égale à `1`
près de `c`. -/
lemma exists_bump {a b c : ℝ} (hc : c ∈ Ioo a b) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ φ a = 0 ∧ φ b = 0 ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ᶠ x in 𝓝 c, φ x = 1) := by
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = min (c - a) (b - c) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by linarith [hc.1]) (by linarith [hc.2])
  have hδa : δ ≤ c - a := by rw [hδ]; exact min_le_left _ _
  have hδb : δ ≤ b - c := by rw [hδ]; exact min_le_right _ _
  let β : ContDiffBump c := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  refine ⟨β, β.contDiff, β.zero_of_le_dist ?_, β.zero_of_le_dist ?_,
    fun x => ⟨β.nonneg, β.le_one⟩, β.eventuallyEq_one⟩
  · show δ / 2 ≤ dist a c
    rw [Real.dist_eq, abs_of_neg (by linarith [hc.1])]
    linarith
  · show δ / 2 ≤ dist b c
    rw [Real.dist_eq, abs_of_pos (by linarith [hc.2])]
    linarith

/-- Il existe `λ > 0` tel que `λ w < 1` sur `[a,b]`. -/
lemma exists_lam {a b c : ℝ} (hc : c ∈ Icc a b) {φ : ℝ → ℝ}
    (hφ01 : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    ∃ lam > 0, ∀ x ∈ Icc a b, lam * wOsc c φ x < 1 := by
  refine ⟨1 / (3 * (b - a) ^ 2 + 1), by positivity, fun x hx => ?_⟩
  have hxc : |x - c| ≤ b - a :=
    abs_le.mpr ⟨by linarith [hx.1, hc.2], by linarith [hx.2, hc.1]⟩
  have hb := hOsc_bounds c x
  have h1 : (x - c) ^ 2 ≤ (b - a) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hxc 2
  have h2 : φ x * hOsc c x ≤ 1 * hOsc c x := mul_le_mul_of_nonneg_right (hφ01 x).2 hb.1
  have hw : wOsc c φ x ≤ 3 * (b - a) ^ 2 := by
    simp only [wOsc]
    linarith
  rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
  linarith

/-- **Remarque 2.6(c).** Soit `L` continue vérifiant (H₂), `f(x) = (x - a)^{1/3}`,
`g = f + 1`, `A = 0`, `B = f(b)`. Alors :
* `f, g ∈ W^{1,1}_T([a,b])` (avec `f'(a) = g'(a) = +∞`) ;
* tout `v ∈ 𝒜_{f,g}` est d'énergie infinie, donc `𝒮_{f,g} = 𝒜_{f,g}` ;
* pour tout `c ∈ ]a,b[`, toute fonction plateau `φ` (lisse, `0 ≤ φ ≤ 1`, `φ(a) = φ(b) = 0`,
  `φ = 1` près de `c`) et tout `λ > 0` tel que `λ w < 1` sur `[a,b]`, la solution
  `v = f + λ φ(x)(x - c)²(2 + sin(1/(x - c)))` n'a pas la régularité partielle de Tonelli ;
* de tels `φ` et `λ` existent.
En particulier, la conjecture de Sychev est fausse sans l'hypothèse d'énergie finie. -/
theorem remark_2_6c {a b : ℝ} (hab : a < b) {L : ℝ → ℝ → ℝ → ℝ}
    (hL : ContinuousOn (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ (univ : Set (ℝ × ℝ))))
    (hH2 : HypH2 a b L) :
    ContinuousOn (fCube a) (Icc a b) ∧ (∀ x ∈ Icc a b, fCube a x < fCube a x + 1) ∧
    TonelliRegular a b (fCube a) ∧ TonelliRegular a b (fun x => fCube a x + 1) ∧
    (∀ v ∈ Admissible a b 0 (fCube a b) (fCube a) (fun x => fCube a x + 1),
      ¬ FiniteEnergy a b L v ∧
        IsSolution a b 0 (fCube a b) L (fCube a) (fun x => fCube a x + 1) v) ∧
    (∀ c ∈ Ioo a b, ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → φ a = 0 → φ b = 0 →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → (∀ᶠ x in 𝓝 c, φ x = 1) →
      ∀ lam > 0, (∀ x ∈ Icc a b, lam * wOsc c φ x < 1) →
        IsSolution a b 0 (fCube a b) L (fCube a) (fun x => fCube a x + 1) (vOsc a c lam φ) ∧
        ¬ TonelliRegular a b (vOsc a c lam φ)) ∧
    (∀ c ∈ Ioo a b, ∃ φ : ℝ → ℝ, (ContDiff ℝ 1 φ ∧ φ a = 0 ∧ φ b = 0 ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧ (∀ᶠ x in 𝓝 c, φ x = 1)) ∧
        ∃ lam > 0, ∀ x ∈ Icc a b, lam * wOsc c φ x < 1) ∧
    (∃ v, IsSolution a b 0 (fCube a b) L (fCube a) (fun x => fCube a x + 1) v ∧
      ¬ TonelliRegular a b v) := by
  have hosc : ∀ c ∈ Ioo a b, ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → φ a = 0 → φ b = 0 →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → (∀ᶠ x in 𝓝 c, φ x = 1) →
      ∀ lam > 0, (∀ x ∈ Icc a b, lam * wOsc c φ x < 1) →
        IsSolution a b 0 (fCube a b) L (fCube a) (fun x => fCube a x + 1) (vOsc a c lam φ) ∧
        ¬ TonelliRegular a b (vOsc a c lam φ) :=
    fun c hc φ hφ hφa hφb hφ01 hφc lam hlam hsmall =>
      ⟨fCube_isSolution hab hL hH2 (vOsc_admissible hab hc hlam hφ hφa hφb hφ01 hsmall),
        vOsc_not_tonelli hc hlam hφc⟩
  have hex : ∀ c ∈ Ioo a b, ∃ φ : ℝ → ℝ, (ContDiff ℝ 1 φ ∧ φ a = 0 ∧ φ b = 0 ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧ (∀ᶠ x in 𝓝 c, φ x = 1)) ∧
        ∃ lam > 0, ∀ x ∈ Icc a b, lam * wOsc c φ x < 1 := by
    intro c hc
    obtain ⟨φ, hφ⟩ := exists_bump hc
    exact ⟨φ, hφ, exists_lam (Ioo_subset_Icc_self hc) hφ.2.2.2.1⟩
  refine ⟨(fCube_continuous a).continuousOn, fun x _ => by linarith, fCube_tonelli hab,
    tonelli_add_const (fCube_tonelli hab),
    fun v hv => ⟨fCube_not_finiteEnergy hab hL hH2 hv, fCube_isSolution hab hL hH2 hv⟩,
    hosc, hex, ?_⟩
  have hc : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  obtain ⟨φ, ⟨hφ, hφa, hφb, hφ01, hφc⟩, lam, hlam, hsmall⟩ := hex _ hc
  exact ⟨_, hosc _ hc φ hφ hφa hφb hφ01 hφc lam hlam hsmall⟩

end TonelliObstacle
