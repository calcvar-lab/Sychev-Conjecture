import Mathlib

/-!
# Section 3 : quasi-concavité près de l'obstacle inférieur (cadre abstrait)

On fixe un intervalle `J = [c,d]` de type inférieur. De la solution `u`, on n'utilise
que les propriétés suivantes, établies en Section 2 :
* `u` est continue sur `J` ;
* l'inégalité (CS) pour les cordes situées au-dessus de `u` (elles sont admissibles
  par le Lemme 2.9, donc les intervalles correspondants sont « bons ») ;
* la monotonie de `Θ` et la borne (2.6) : `Θ(K,ε) ≤ C(K) ε^γ(K)`.
-/

open Set Filter Topology

noncomputable section

namespace TonelliObstacle

/-- Hypothèses du cadre abstrait sur l'intervalle `J = [c,d]` de type inférieur. -/
structure LowerFrame (u : ℝ → ℝ) (c d : ℝ) (Θ : ℝ → ℝ → ℝ) : Prop where
  lt : c < d
  cont : ContinuousOn u (Icc c d)
  nonneg : ∀ K ε, 0 ≤ Θ K ε
  mono : ∀ K K' ε ε', K ≤ K' → ε ≤ ε' → Θ K ε ≤ Θ K' ε'
  holder : ∀ K, ∃ C γ : ℝ, 0 < γ ∧ ∀ ε, 0 < ε → Θ K ε ≤ C * ε ^ γ
  cs : ∀ σ τ, c ≤ σ → σ < τ → τ ≤ d →
    (∀ x ∈ Icc σ τ, u x ≤ u σ + slope u σ τ * (x - σ)) →
    ∀ s t, σ ≤ s → s < t → t ≤ τ →
      |u t - u s - slope u σ τ * (t - s)| ≤
        Θ |slope u σ τ| (τ - σ) * Real.sqrt ((τ - σ) * (t - s))

/-- La fonction `E(K,r) = 4 ∑_j Θ(K, 2^{-j} r)`. -/
def E (Θ : ℝ → ℝ → ℝ) (K r : ℝ) : ℝ :=
  4 * ∑' j : ℕ, Θ K (r / 2 ^ j)

variable {u : ℝ → ℝ} {c d : ℝ} {Θ : ℝ → ℝ → ℝ}

/-! ## Conséquences de (2.6) -/

/-- `Θ(K,ε) → 0` quand `ε → 0⁺`. -/
lemma LowerFrame.theta_tendsto_zero (hF : LowerFrame u c d Θ) (K : ℝ) :
    Tendsto (fun ε => Θ K ε) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, γ, hγ, hC⟩ := hF.holder K
  -- C ε^γ → 0 quand ε → 0⁺
  have hlim : Tendsto (fun ε : ℝ => C * ε ^ γ) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => ε ^ γ) (𝓝 0) (𝓝 0) := by
      have := Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)
      simpa [Real.zero_rpow hγ.ne'] using this.tendsto
    have h2 := h1.const_mul C
    rw [mul_zero] at h2
    exact tendsto_nhdsWithin_of_tendsto_nhds h2
  -- encadrement : 0 ≤ Θ(K,ε) ≤ C ε^γ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Eventually.of_forall (fun ε => hF.nonneg K ε)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hC ε hε

/-- Borne géométrique : `Θ(K, 2^{-j} r) ≤ C r^γ q^j` avec `q = 2^{-γ} < 1`. -/
lemma LowerFrame.theta_geom_bound (hF : LowerFrame u c d Θ) (K : ℝ) :
    ∃ C γ : ℝ, 0 < γ ∧ ∀ r, 0 < r → ∀ j : ℕ,
      Θ K (r / 2 ^ j) ≤ C * r ^ γ * ((2 : ℝ) ^ γ)⁻¹ ^ j := by
  obtain ⟨C, γ, hγ, hC⟩ := hF.holder K
  refine ⟨C, γ, hγ, fun r hr j => ?_⟩
  have hpos : 0 < r / 2 ^ j := by positivity
  -- (2^j)^γ = (2^γ)^j
  have h2 : ((2 : ℝ) ^ j) ^ γ = ((2 : ℝ) ^ γ) ^ j := by
    rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_natCast ((2 : ℝ) ^ γ) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
  calc Θ K (r / 2 ^ j) ≤ C * (r / 2 ^ j) ^ γ := hC _ hpos
    _ = C * r ^ γ * ((2 : ℝ) ^ γ)⁻¹ ^ j := by
      rw [Real.div_rpow hr.le (by positivity), h2, inv_pow]
      ring

/-- La série `∑_j Θ(K, 2^{-j} r)` converge. -/
lemma LowerFrame.summable_theta (hF : LowerFrame u c d Θ) (K r : ℝ) (hr : 0 < r) :
    Summable (fun j : ℕ => Θ K (r / 2 ^ j)) := by
  obtain ⟨C, γ, hγ, hb⟩ := hF.theta_geom_bound K
  have hq1 : ((2 : ℝ) ^ γ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) hγ)
  have hq0 : 0 ≤ ((2 : ℝ) ^ γ)⁻¹ := by positivity
  exact Summable.of_nonneg_of_le (fun j => hF.nonneg _ _) (hb r hr)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left (C * r ^ γ))

/-- `E(K,r) → 0` quand `r → 0⁺` (série géométrique). -/
lemma LowerFrame.E_tendsto_zero (hF : LowerFrame u c d Θ) (K : ℝ) :
    Tendsto (fun r => E Θ K r) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, γ, hγ, hb⟩ := hF.theta_geom_bound K
  set q : ℝ := ((2 : ℝ) ^ γ)⁻¹ with hq
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) hγ)
  have hq0 : 0 ≤ q := by positivity
  -- 4 C (1-q)⁻¹ r^γ → 0
  have hlim : Tendsto (fun r : ℝ => 4 * (C * r ^ γ * (1 - q)⁻¹)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => r ^ γ) (𝓝 0) (𝓝 0) := by
      have := Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)
      simpa [Real.zero_rpow hγ.ne'] using this.tendsto
    have h2 := ((h1.const_mul C).mul_const (1 - q)⁻¹).const_mul 4
    simp only [mul_zero, zero_mul] at h2
    exact tendsto_nhdsWithin_of_tendsto_nhds h2
  -- encadrement : 0 ≤ E(K,r) ≤ 4 C (1-q)⁻¹ r^γ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_nonneg (by norm_num) (tsum_nonneg (fun j => hF.nonneg _ _))
  · filter_upwards [self_mem_nhdsWithin] with r hr
    unfold E
    have hgeo := summable_geometric_of_lt_one hq0 hq1
    have hle : ∑' j : ℕ, Θ K (r / 2 ^ j) ≤ ∑' j : ℕ, C * r ^ γ * q ^ j :=
      Summable.tsum_le_tsum (hb r hr) (hF.summable_theta K r hr) (hgeo.mul_left _)
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1] at hle
    linarith

/-! ## Lemme 3.1 : quasi-concavité -/

/-- **Lemme 3.1**, inégalité (3.1). -/
lemma LowerFrame.approx_concave (hF : LowerFrame u c d Θ) {x y z : ℝ}
    (hcx : c ≤ x) (hxy : x < y) (hyz : y < z) (hzd : z ≤ d) :
    u x + slope u x z * (y - x) - u y ≤
      Θ |slope u x z| (z - x) * Real.sqrt ((z - x) * min (y - x) (z - y)) := by
  -- k := k(x,z) ; la corde de u sur [x,z] est t ↦ u(x) + k (t - x)
  obtain ⟨k, hk⟩ : ∃ k, slope u x z = k := ⟨_, rfl⟩
  rw [hk]
  have hkz : (z - x) * k = u z - u x := by
    rw [← hk]
    simpa using sub_smul_slope u x z
  -- cas trivial : u(y) est au-dessus de la corde
  by_cases hy : u x + k * (y - x) ≤ u y
  · have h1 : 0 ≤ Θ |k| (z - x) * Real.sqrt ((z - x) * min (y - x) (z - y)) :=
      mul_nonneg (hF.nonneg _ _) (Real.sqrt_nonneg _)
    linarith
  push Not at hy
  -- g = u - corde : continue sur [x,z], nulle en x et z, < 0 en y
  obtain ⟨g, hg_def⟩ : ∃ g : ℝ → ℝ, g = fun t => u t - (u x + k * (t - x)) := ⟨_, rfl⟩
  have hgval : ∀ t, g t = u t - (u x + k * (t - x)) := fun t => by rw [hg_def]
  have hu : ContinuousOn u (Icc x z) := hF.cont.mono (Icc_subset_Icc hcx hzd)
  have hg : ContinuousOn g (Icc x z) := by
    rw [hg_def]
    fun_prop
  have hgx : g x = 0 := by rw [hgval]; ring
  have hgz : g z = 0 := by rw [hgval]; linear_combination -hkz
  have hgy : g y < 0 := by rw [hgval]; linarith
  -- σ := sup {t ∈ [x,y] : g(t) ≥ 0}
  set S : Set ℝ := Icc x y ∩ g ⁻¹' Ici 0 with hS_def
  have hS : IsClosed S :=
    (hg.mono (Icc_subset_Icc le_rfl hyz.le)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici
  have hxS : x ∈ S := ⟨⟨le_rfl, hxy.le⟩, by simp [hgx]⟩
  have hSbdd : BddAbove S := ⟨y, fun t ht => ht.1.2⟩
  set σ := sSup S with hσ_def
  have hσS : σ ∈ S := hS.csSup_mem ⟨x, hxS⟩ hSbdd
  have hσ_max : ∀ t ∈ S, t ≤ σ := fun t ht => le_csSup hSbdd ht
  -- τ := inf {t ∈ [y,z] : g(t) ≥ 0}
  set T : Set ℝ := Icc y z ∩ g ⁻¹' Ici 0 with hT_def
  have hT : IsClosed T :=
    (hg.mono (Icc_subset_Icc hxy.le le_rfl)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici
  have hzT : z ∈ T := ⟨⟨hyz.le, le_rfl⟩, by simp [hgz]⟩
  have hTbdd : BddBelow T := ⟨y, fun t ht => ht.1.1⟩
  set τ := sInf T with hτ_def
  have hτT : τ ∈ T := hT.csInf_mem ⟨z, hzT⟩ hTbdd
  have hτ_min : ∀ t ∈ T, τ ≤ t := fun t ht => csInf_le hTbdd ht
  have hxσ : x ≤ σ := hσS.1.1
  have hσy : σ ≤ y := hσS.1.2
  have hyτ : y ≤ τ := hτT.1.1
  have hτz : τ ≤ z := hτT.1.2
  have hgσ : 0 ≤ g σ := hσS.2
  have hgτ : 0 ≤ g τ := hτT.2
  -- g(σ) = 0 et g(τ) = 0, par le théorème des valeurs intermédiaires
  have hgσ0 : g σ = 0 := by
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' hσy
      (hg.mono (Icc_subset_Icc hxσ hyz.le))
      (show (0 : ℝ) ∈ Icc (g y) (g σ) from ⟨hgy.le, hgσ⟩)
    have htS : t ∈ S := ⟨⟨hxσ.trans ht.1, ht.2⟩, by simp [hgt]⟩
    have htσ : t = σ := le_antisymm (hσ_max t htS) ht.1
    rw [← htσ]
    exact hgt
  have hgτ0 : g τ = 0 := by
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc hyτ
      (hg.mono (Icc_subset_Icc hxy.le hτz))
      (show (0 : ℝ) ∈ Icc (g y) (g τ) from ⟨hgy.le, hgτ⟩)
    have htT : t ∈ T := ⟨⟨ht.1, ht.2.trans hτz⟩, by simp [hgt]⟩
    have htτ : t = τ := le_antisymm ht.2 (hτ_min t htT)
    rw [← htτ]
    exact hgt
  have hσy' : σ < y := lt_of_le_of_ne hσy (fun h => by rw [h] at hgσ0; linarith)
  have hyτ' : y < τ := lt_of_le_of_ne hyτ (fun h => by rw [← h] at hgτ0; linarith)
  have hστ : σ < τ := hσy'.trans hyτ'
  have huσ : u σ = u x + k * (σ - x) := by have := hgval σ; linarith
  have huτ : u τ = u x + k * (τ - x) := by have := hgval τ; linarith
  -- la corde de u sur [σ,τ] a la même pente k
  have hst : (τ - σ) * slope u σ τ = u τ - u σ := by
    simpa using sub_smul_slope u σ τ
  have hslope : slope u σ τ = k := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hστ.ne')
    rw [hst, huσ, huτ]
    ring
  -- sur [σ,τ], u est sous sa corde (g ≤ 0)
  have habove : ∀ t ∈ Icc σ τ, u t ≤ u σ + slope u σ τ * (t - σ) := by
    intro t ht
    have hgt : g t ≤ 0 := by
      by_contra hcon
      push Not at hcon
      rcases le_total t y with hty | hty
      · have htS : t ∈ S := ⟨⟨hxσ.trans ht.1, hty⟩, by simp [hcon.le]⟩
        have htσ : t = σ := le_antisymm (hσ_max t htS) ht.1
        rw [htσ] at hcon
        linarith
      · have htT : t ∈ T := ⟨⟨hty, ht.2.trans hτz⟩, by simp [hcon.le]⟩
        have htτ : t = τ := le_antisymm ht.2 (hτ_min t htT)
        rw [htτ] at hcon
        linarith
    rw [hslope, huσ]
    have := hgval t
    nlinarith
  -- (CS) sur le bon intervalle [σ,τ], avec (s,t) = (σ,y) puis (y,τ)
  have hcs := hF.cs σ τ (hcx.trans hxσ) hστ (hτz.trans hzd) habove
  rw [hslope] at hcs
  have hA := hcs σ y le_rfl hσy' hyτ'.le
  have hB := hcs y τ hσy'.le hyτ' le_rfl
  have hLA : u x + k * (y - x) - u y ≤
      Θ |k| (τ - σ) * Real.sqrt ((τ - σ) * (y - σ)) := by
    have := neg_le_abs (u y - u σ - k * (y - σ))
    linarith
  have hLB : u x + k * (y - x) - u y ≤
      Θ |k| (τ - σ) * Real.sqrt ((τ - σ) * (τ - y)) := by
    have := le_abs_self (u τ - u y - k * (τ - y))
    linarith
  -- conclusion : monotonie de Θ et de la racine
  have hΘ : Θ |k| (τ - σ) ≤ Θ |k| (z - x) := hF.mono _ _ _ _ le_rfl (by linarith)
  rcases le_total (y - x) (z - y) with hm | hm
  · rw [min_eq_left hm]
    have hsq : Real.sqrt ((τ - σ) * (y - σ)) ≤ Real.sqrt ((z - x) * (y - x)) :=
      Real.sqrt_le_sqrt (mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith))
    have := mul_le_mul hΘ hsq (Real.sqrt_nonneg _) (hF.nonneg _ _)
    linarith
  · rw [min_eq_right hm]
    have hsq : Real.sqrt ((τ - σ) * (τ - y)) ≤ Real.sqrt ((z - x) * (z - y)) :=
      Real.sqrt_le_sqrt (mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith))
    have := mul_le_mul hΘ hsq (Real.sqrt_nonneg _) (hF.nonneg _ _)
    linarith

/-- **Lemme 3.1 (a)**. -/
lemma LowerFrame.approx_concave_right (hF : LowerFrame u c d Θ) {x ρ θ : ℝ}
    (hcx : c ≤ x) (hρ : 0 < ρ) (hxd : x + ρ ≤ d) (hθ : θ ∈ Icc (1 / 4 : ℝ) 1) :
    slope u x (x + ρ) - 2 * Θ |slope u x (x + ρ)| ρ ≤ slope u x (x + θ * ρ) := by
  have hθpos : 0 < θ := by linarith [hθ.1]
  rcases eq_or_lt_of_le hθ.2 with h1 | h1
  · -- θ = 1 : rien à démontrer
    subst h1
    simp only [one_mul]
    linarith [hF.nonneg |slope u x (x + ρ)| ρ]
  · -- θ < 1 : on applique (3.1) avec y = x + θρ et z = x + ρ
    have hθρ : 0 < θ * ρ := mul_pos hθpos hρ
    have hxy : x < x + θ * ρ := by linarith
    have hyz : x + θ * ρ < x + ρ := by nlinarith
    have h0 := hF.approx_concave hcx hxy hyz hxd
    have e1 : x + θ * ρ - x = θ * ρ := by ring
    have e2 : x + ρ - x = ρ := by ring
    have e3 : x + ρ - (x + θ * ρ) = (1 - θ) * ρ := by ring
    rw [e1, e2, e3] at h0
    -- u(y) - u(x) = θρ k(x,y)
    have hy : (x + θ * ρ - x) * slope u x (x + θ * ρ) = u (x + θ * ρ) - u x := by
      simpa using sub_smul_slope u x (x + θ * ρ)
    rw [e1] at hy
    -- √(ρ min(θρ, (1-θ)ρ)) ≤ 2θρ, car θ ≥ 1/4
    have hs : Real.sqrt (ρ * min (θ * ρ) ((1 - θ) * ρ)) ≤ 2 * (θ * ρ) := by
      have hm : ρ * min (θ * ρ) ((1 - θ) * ρ) ≤ ρ * (θ * ρ) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hρ.le
      have h4 : 0 ≤ θ * ρ ^ 2 * (4 * θ - 1) :=
        mul_nonneg (mul_nonneg hθpos.le (sq_nonneg ρ)) (by linarith [hθ.1])
      have h1' : ρ * min (θ * ρ) ((1 - θ) * ρ) ≤ (2 * (θ * ρ)) ^ 2 := by nlinarith
      calc Real.sqrt (ρ * min (θ * ρ) ((1 - θ) * ρ))
          ≤ Real.sqrt ((2 * (θ * ρ)) ^ 2) := Real.sqrt_le_sqrt h1'
        _ = 2 * (θ * ρ) := Real.sqrt_sq (by linarith)
    have h2 := mul_le_mul_of_nonneg_left hs (hF.nonneg |slope u x (x + ρ)| ρ)
    -- on multiplie la conclusion par θρ > 0
    have key : θ * ρ * (slope u x (x + ρ) - 2 * Θ |slope u x (x + ρ)| ρ)
        ≤ θ * ρ * slope u x (x + θ * ρ) := by nlinarith
    exact le_of_mul_le_mul_left key hθρ

/-- **Lemme 3.1 (b)**. -/
lemma LowerFrame.approx_concave_left (hF : LowerFrame u c d Θ) {x ρ θ : ℝ}
    (hcx : c ≤ x - ρ) (hρ : 0 < ρ) (hxd : x ≤ d) (hθ : θ ∈ Icc (1 / 4 : ℝ) 1) :
    slope u (x - θ * ρ) x ≤ slope u (x - ρ) x + 2 * Θ |slope u (x - ρ) x| ρ := by
  have hθpos : 0 < θ := by linarith [hθ.1]
  rcases eq_or_lt_of_le hθ.2 with h1 | h1
  · -- θ = 1 : rien à démontrer
    subst h1
    simp only [one_mul]
    linarith [hF.nonneg |slope u (x - ρ) x| ρ]
  · -- θ < 1 : on applique (3.1) aux points x - ρ < x - θρ < x
    have hθρ : 0 < θ * ρ := mul_pos hθpos hρ
    have hxy : x - ρ < x - θ * ρ := by nlinarith
    have hyz : x - θ * ρ < x := by linarith
    have h0 := hF.approx_concave hcx hxy hyz hxd
    have e1 : x - θ * ρ - (x - ρ) = (1 - θ) * ρ := by ring
    have e2 : x - (x - ρ) = ρ := by ring
    have e3 : x - (x - θ * ρ) = θ * ρ := by ring
    rw [e1, e2, e3] at h0
    -- u(x) - u(x - ρ) = ρ k(x - ρ, x)  et  u(x) - u(x - θρ) = θρ k(x - θρ, x)
    have hK : (x - (x - ρ)) * slope u (x - ρ) x = u x - u (x - ρ) := by
      simpa using sub_smul_slope u (x - ρ) x
    rw [e2] at hK
    have hy : (x - (x - θ * ρ)) * slope u (x - θ * ρ) x = u x - u (x - θ * ρ) := by
      simpa using sub_smul_slope u (x - θ * ρ) x
    rw [e3] at hy
    -- √(ρ min((1-θ)ρ, θρ)) ≤ 2θρ, car θ ≥ 1/4
    have hs : Real.sqrt (ρ * min ((1 - θ) * ρ) (θ * ρ)) ≤ 2 * (θ * ρ) := by
      have hm : ρ * min ((1 - θ) * ρ) (θ * ρ) ≤ ρ * (θ * ρ) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hρ.le
      have h4 : 0 ≤ θ * ρ ^ 2 * (4 * θ - 1) :=
        mul_nonneg (mul_nonneg hθpos.le (sq_nonneg ρ)) (by linarith [hθ.1])
      have h1' : ρ * min ((1 - θ) * ρ) (θ * ρ) ≤ (2 * (θ * ρ)) ^ 2 := by nlinarith
      calc Real.sqrt (ρ * min ((1 - θ) * ρ) (θ * ρ))
          ≤ Real.sqrt ((2 * (θ * ρ)) ^ 2) := Real.sqrt_le_sqrt h1'
        _ = 2 * (θ * ρ) := Real.sqrt_sq (by linarith)
    have h2 := mul_le_mul_of_nonneg_left hs (hF.nonneg |slope u (x - ρ) x| ρ)
    -- on multiplie la conclusion par θρ > 0
    have key : θ * ρ * slope u (x - θ * ρ) x
        ≤ θ * ρ * (slope u (x - ρ) x + 2 * Θ |slope u (x - ρ) x| ρ) := by nlinarith
    exact le_of_mul_le_mul_left key hθρ

/-- **Lemme 3.1 (c)**. -/
lemma LowerFrame.approx_concave_center (hF : LowerFrame u c d Θ) {x h h' : ℝ}
    (hh : 0 < h) (hh' : 0 < h') (hcx : c ≤ x - h) (hxd : x + h' ≤ d) :
    h * h' / (h + h') * (slope u x (x + h') - slope u (x - h) x) ≤
      Θ |slope u (x - h) (x + h')| (h + h') * Real.sqrt ((h + h') * min h h') := by
  -- on applique (3.1) aux points x - h < x < x + h'
  have hxy : x - h < x := by linarith
  have hyz : x < x + h' := by linarith
  have h0 := hF.approx_concave hcx hxy hyz hxd
  have e1 : x - (x - h) = h := by ring
  have e2 : x + h' - (x - h) = h + h' := by ring
  have e3 : x + h' - x = h' := by ring
  rw [e1, e2, e3] at h0
  -- les trois relations « longueur × pente = accroissement »
  have hK : (x + h' - (x - h)) * slope u (x - h) (x + h') = u (x + h') - u (x - h) := by
    simpa using sub_smul_slope u (x - h) (x + h')
  rw [e2] at hK
  have hR : (x + h' - x) * slope u x (x + h') = u (x + h') - u x := by
    simpa using sub_smul_slope u x (x + h')
  rw [e3] at hR
  have hL : (x - (x - h)) * slope u (x - h) x = u x - u (x - h) := by
    simpa using sub_smul_slope u (x - h) x
  rw [e1] at hL
  -- le membre de gauche de (3.1) est exactement hh'/(h+h') (k_R - k_L)
  have hsum : 0 < h + h' := by linarith
  have heq : h * h' / (h + h') * (slope u x (x + h') - slope u (x - h) x)
      = u (x - h) + slope u (x - h) (x + h') * h - u x := by
    rw [div_mul_eq_mul_div, div_eq_iff hsum.ne']
    linear_combination (-h) * hK + h * hR + (-h') * hL
  rw [heq]
  exact h0

/-! ## Lemme 3.2 : monotonie unilatérale des pentes -/

/-- Lemme 3.1 (a), reformulé avec `t = θρ` : si `t ≤ ρ ≤ 4t`, alors
`k(x,x+t) ≥ k(x,x+ρ) - 2 Θ(|k(x,x+ρ)|, ρ)`. -/
lemma LowerFrame.approx_concave_right' (hF : LowerFrame u c d Θ) {x t ρ : ℝ}
    (hcx : c ≤ x) (ht : 0 < t) (htρ : t ≤ ρ) (hρt : ρ ≤ 4 * t) (hxd : x + ρ ≤ d) :
    slope u x (x + ρ) - 2 * Θ |slope u x (x + ρ)| ρ ≤ slope u x (x + t) := by
  have hρ : 0 < ρ := ht.trans_le htρ
  have hθ : t / ρ ∈ Icc (1 / 4 : ℝ) 1 := by
    constructor
    · rw [le_div_iff₀ hρ]; linarith
    · rw [div_le_iff₀ hρ]; linarith
  have h := hF.approx_concave_right hcx hρ hxd hθ
  have e : t / ρ * ρ = t := by field_simp
  rw [e] at h
  exact h

/-- `e₀ + ∑_{i<j} e_i ≤ E(K,r)`, avec `e_i = 2 Θ(K, 2^{-i} r)`. -/
lemma LowerFrame.partial_le_E (hF : LowerFrame u c d Θ) (K r : ℝ) (hr : 0 < r) (j : ℕ) :
    2 * Θ K r + ∑ i ∈ Finset.range j, 2 * Θ K (r / 2 ^ i) ≤ E Θ K r := by
  have hs := hF.summable_theta K r hr
  have h0 : Θ K r ≤ ∑' i : ℕ, Θ K (r / 2 ^ i) := by
    have := hs.le_tsum 0 (fun i _ => hF.nonneg _ _)
    simpa using this
  have h1 : ∑ i ∈ Finset.range j, Θ K (r / 2 ^ i) ≤ ∑' i : ℕ, Θ K (r / 2 ^ i) :=
    hs.sum_le_tsum _ (fun i _ => hF.nonneg _ _)
  rw [← Finset.mul_sum]
  unfold E
  linarith

/-- **Lemme 3.2 (a)**. -/
lemma LowerFrame.slope_mono_right (hF : LowerFrame u c d Θ) {x ℓ r : ℝ}
    (hr : 0 < r) (hcx : c ≤ x) (hxd : x + r ≤ d)
    (hE : E Θ (|ℓ| + 1) r ≤ 1) (hℓ : ℓ ≤ slope u x (x + r)) :
    ∀ ρ ∈ Ioc 0 r, ℓ - E Θ (|ℓ| + 1) r ≤ slope u x (x + ρ) := by
  set M := |ℓ| + 1 with hM
  -- faits élémentaires sur les r / 2^j
  have hpow : ∀ j : ℕ, (0 : ℝ) < r / 2 ^ j := fun j => by positivity
  have hhalf : ∀ j : ℕ, r / 2 ^ (j + 1) = r / 2 ^ j / 2 := fun j => by
    rw [pow_succ, div_div]
  have hle : ∀ j : ℕ, r / 2 ^ (j + 1) ≤ r / 2 ^ j := fun j => by
    rw [hhalf j]; linarith [hpow j]
  have hDr : ∀ j : ℕ, r / 2 ^ j ≤ r := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [hhalf j]; linarith [hpow j]
  -- φ(ρ) = k(x, x+ρ) est continue sur ]0, r]
  have hφ : ContinuousOn (fun ρ => slope u x (x + ρ)) (Ioc 0 r) := by
    have hadd : ContinuousOn (fun ρ : ℝ => x + ρ) (Ioc 0 r) := by fun_prop
    have hmaps : MapsTo (fun ρ : ℝ => x + ρ) (Ioc 0 r) (Icc c d) := fun ρ hρ => by
      simp only [mem_Icc]
      constructor <;> linarith [hρ.1, hρ.2]
    have hux : ContinuousOn (fun ρ => u (x + ρ)) (Ioc 0 r) := hF.cont.comp hadd hmaps
    have heq : (fun ρ => slope u x (x + ρ)) = fun ρ => (u (x + ρ) - u x) / ρ := by
      funext ρ
      rw [slope_def_field]
      congr 1
      ring
    rw [heq]
    exact (hux.sub continuousOn_const).div continuousOn_id (fun ρ hρ => hρ.1.ne')
  -- sur D_j = [r/2^(j+1), r/2^j], φ atteint son minimum en un point t_j
  have hD : ∀ j : ℕ, ∃ t ∈ Icc (r / 2 ^ (j + 1)) (r / 2 ^ j),
      IsMinOn (fun ρ => slope u x (x + ρ)) (Icc (r / 2 ^ (j + 1)) (r / 2 ^ j)) t := by
    intro j
    apply isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (hle j))
    exact hφ.mono (fun ρ hρ => ⟨lt_of_lt_of_le (hpow (j + 1)) hρ.1, hρ.2.trans (hDr j)⟩)
  choose t ht hmin using hD
  have htpos : ∀ j, 0 < t j := fun j => lt_of_lt_of_le (hpow (j + 1)) (ht j).1
  have htr : ∀ j, t j ≤ r := fun j => (ht j).2.trans (hDr j)
  have hmin' : ∀ j, ∀ ρ ∈ Icc (r / 2 ^ (j + 1)) (r / 2 ^ j),
      slope u x (x + t j) ≤ slope u x (x + ρ) :=
    fun j ρ hρ => isMinOn_iff.mp (hmin j) ρ hρ
  have hsum : ∀ j, 2 * Θ M r + ∑ i ∈ Finset.range j, 2 * Θ M (r / 2 ^ i) ≤ E Θ M r :=
    hF.partial_le_E M r hr
  have hs0 : ∀ j, 0 ≤ ∑ i ∈ Finset.range j, 2 * Θ M (r / 2 ^ i) := fun j =>
    Finset.sum_nonneg (fun i _ => by linarith [hF.nonneg M (r / 2 ^ i)])
  -- (P_j) : m_j ≥ ℓ - e₀ - ∑_{i<j} e_i, par récurrence
  have hP : ∀ j : ℕ, ℓ - (2 * Θ M r + ∑ i ∈ Finset.range j, 2 * Θ M (r / 2 ^ i))
      ≤ slope u x (x + t j) := by
    intro j
    induction j with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, add_zero]
      by_cases h0 : ℓ ≤ slope u x (x + t 0)
      · linarith [hF.nonneg M r]
      push Not at h0
      -- valeurs intermédiaires sur [t₀, r] : φ(ρ') = ℓ
      have hφ0 : ContinuousOn (fun ρ => slope u x (x + ρ)) (Icc (t 0) r) :=
        hφ.mono (fun ρ hρ => ⟨lt_of_lt_of_le (htpos 0) hρ.1, hρ.2⟩)
      obtain ⟨ρ', hρ', hφρ'⟩ := intermediate_value_Icc (htr 0) hφ0
        (show ℓ ∈ Icc (slope u x (x + t 0)) (slope u x (x + r)) from ⟨h0.le, hℓ⟩)
      have hφρ'' : slope u x (x + ρ') = ℓ := hφρ'
      have ht0 : r / 2 ≤ t 0 := by
        have := (ht 0).1
        simpa using this
      have key := hF.approx_concave_right' hcx (htpos 0) hρ'.1
        (by linarith [hρ'.2]) (by linarith [hρ'.2])
      rw [hφρ''] at key
      have hmono : Θ |ℓ| ρ' ≤ Θ M r := hF.mono _ _ _ _ (by linarith [hM]) hρ'.2
      linarith
    | succ j ih =>
      rw [Finset.sum_range_succ]
      by_cases h1 : ℓ ≤ slope u x (x + t (j + 1))
      · linarith [hF.nonneg M r, hF.nonneg M (r / 2 ^ j), hs0 j]
      push Not at h1
      by_cases h2 : ℓ < slope u x (x + t j)
      · -- cas m_j > ℓ : valeurs intermédiaires sur [t_{j+1}, r/2^(j+1)]
        have hb : r / 2 ^ (j + 1) ∈ Icc (r / 2 ^ (j + 1)) (r / 2 ^ j) := ⟨le_rfl, hle j⟩
        have hφb := hmin' j _ hb
        have hφ1 : ContinuousOn (fun ρ => slope u x (x + ρ)) (Icc (t (j + 1)) (r / 2 ^ (j + 1))) :=
          hφ.mono (fun ρ hρ => ⟨lt_of_lt_of_le (htpos (j + 1)) hρ.1, hρ.2.trans (hDr (j + 1))⟩)
        obtain ⟨ρ', hρ', hφρ'⟩ := intermediate_value_Icc (ht (j + 1)).2 hφ1
          (show ℓ ∈ Icc (slope u x (x + t (j + 1))) (slope u x (x + r / 2 ^ (j + 1))) from
            ⟨h1.le, by linarith⟩)
        have hφρ'' : slope u x (x + ρ') = ℓ := hφρ'
        have key := hF.approx_concave_right' hcx (htpos (j + 1)) hρ'.1
          (by linarith [hρ'.2, hhalf (j + 1), (ht (j + 1)).1, htpos (j + 1)])
          (by linarith [hρ'.2, hDr (j + 1)])
        rw [hφρ''] at key
        have hmono : Θ |ℓ| ρ' ≤ Θ M r :=
          hF.mono _ _ _ _ (by linarith [hM]) (by linarith [hρ'.2, hDr (j + 1)])
        linarith [hF.nonneg M (r / 2 ^ j), hs0 j]
      · -- cas m_j ≤ ℓ : on a |m_j| ≤ M, et on applique 3.1 (a) avec ρ = t_j
        push Not at h2
        have hlow : ℓ - 1 ≤ slope u x (x + t j) := by linarith [hsum j]
        have habs : |slope u x (x + t j)| ≤ M := by
          rw [abs_le]
          refine ⟨?_, ?_⟩ <;> linarith [neg_abs_le ℓ, le_abs_self ℓ, hM]
        have key := hF.approx_concave_right' (ρ := t j) hcx (htpos (j + 1))
          (by linarith [(ht (j + 1)).2, (ht j).1])
          (by linarith [(ht j).2, hhalf j, hhalf (j + 1), (ht (j + 1)).1])
          (by linarith [htr j])
        have hmono : Θ |slope u x (x + t j)| (t j) ≤ Θ M (r / 2 ^ j) :=
          hF.mono _ _ _ _ habs (ht j).2
        linarith
  -- conclusion : tout ρ ∈ ]0,r] appartient à un D_n
  intro ρ hρ
  have hρ1 : (1 : ℝ) ≤ r / ρ := by
    rw [le_div_iff₀ hρ.1]; linarith [hρ.2]
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hρ1 (by norm_num : (1 : ℝ) < 2)
  have hρn : ρ ≤ r / 2 ^ n := by
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hρ.1] at hn1
    linarith
  have hρn1 : r / 2 ^ (n + 1) ≤ ρ := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hρ.1] at hn2
    linarith
  have h1 := hmin' n ρ ⟨hρn1, hρn⟩
  have h2 := hP n
  have h3 := hsum n
  linarith

/-- Pentes et symétrie `y ↦ c + d - y` : `k_ũ(x̃, x̃+ρ) = -k_u(x-ρ, x)`. -/
lemma slope_reflect (u : ℝ → ℝ) (c d x ρ : ℝ) :
    slope (fun y => u (c + d - y)) (c + d - x) (c + d - x + ρ) = - slope u (x - ρ) x := by
  rw [slope_def_field, slope_def_field]
  have e1 : c + d - (c + d - x + ρ) = x - ρ := by ring
  have e2 : c + d - (c + d - x) = x := by ring
  simp only [e1, e2]
  have e3 : c + d - x + ρ - (c + d - x) = ρ := by ring
  have e4 : x - (x - ρ) = ρ := by ring
  rw [e3, e4]
  ring

/-- **Symétrie (S₂)** : si `u` vérifie le cadre sur `[c,d]`, alors `ũ = u(c + d - ·)` aussi,
avec la même fonction `Θ`. -/
lemma LowerFrame.reflect (hF : LowerFrame u c d Θ) :
    LowerFrame (fun y => u (c + d - y)) c d Θ where
  lt := hF.lt
  cont := by
    have hmaps : MapsTo (fun y : ℝ => c + d - y) (Icc c d) (Icc c d) := fun y hy => by
      simp only [mem_Icc]
      constructor <;> linarith [hy.1, hy.2]
    exact hF.cont.comp (by fun_prop) hmaps
  nonneg := hF.nonneg
  mono := hF.mono
  holder := hF.holder
  cs := by
    intro σ τ hcσ hστ hτd habove s t hσs hst htτ
    show |u (c + d - t) - u (c + d - s) - slope (fun y => u (c + d - y)) σ τ * (t - s)| ≤
      Θ |slope (fun y => u (c + d - y)) σ τ| (τ - σ) * Real.sqrt ((τ - σ) * (t - s))
    -- la pente de ũ sur [σ,τ] est l'opposée de celle de u sur [c+d-τ, c+d-σ]
    have h1 : (τ - σ) * slope (fun y => u (c + d - y)) σ τ
        = u (c + d - τ) - u (c + d - σ) := by
      simpa using sub_smul_slope (fun y => u (c + d - y)) σ τ
    have h2 : (c + d - σ - (c + d - τ)) * slope u (c + d - τ) (c + d - σ)
        = u (c + d - σ) - u (c + d - τ) := by
      simpa using sub_smul_slope u (c + d - τ) (c + d - σ)
    have h3 : c + d - σ - (c + d - τ) = τ - σ := by ring
    rw [h3] at h2
    have hk : slope (fun y => u (c + d - y)) σ τ = - slope u (c + d - τ) (c + d - σ) := by
      apply mul_left_cancel₀ (sub_ne_zero.mpr hστ.ne')
      rw [h1, mul_neg, h2]
      ring
    -- u est sous sa corde sur [c+d-τ, c+d-σ]
    have habove' : ∀ y ∈ Icc (c + d - τ) (c + d - σ),
        u y ≤ u (c + d - τ) + slope u (c + d - τ) (c + d - σ) * (y - (c + d - τ)) := by
      intro y hy
      have hx : c + d - y ∈ Icc σ τ := ⟨by linarith [hy.2], by linarith [hy.1]⟩
      have := habove (c + d - y) hx
      simp only [sub_sub_cancel] at this
      rw [hk] at this
      linarith
    -- (CS) pour u sur [c+d-τ, c+d-σ], avec (s', t') = (c+d-t, c+d-s)
    have hcs := hF.cs (c + d - τ) (c + d - σ) (by linarith) (by linarith) (by linarith)
      habove' (c + d - t) (c + d - s) (by linarith) (by linarith) (by linarith)
    have e1 : c + d - σ - (c + d - τ) = τ - σ := by ring
    have e2 : c + d - s - (c + d - t) = t - s := by ring
    rw [e1, e2] at hcs
    rw [hk, abs_neg]
    have e3 : u (c + d - t) - u (c + d - s) - -slope u (c + d - τ) (c + d - σ) * (t - s)
        = -(u (c + d - s) - u (c + d - t) - slope u (c + d - τ) (c + d - σ) * (t - s)) := by
      ring
    rw [e3, abs_neg]
    exact hcs

/-- **Lemme 3.2 (b)**, déduit du (a) par la symétrie (S₂). -/
lemma LowerFrame.slope_mono_left (hF : LowerFrame u c d Θ) {x ℓ r : ℝ}
    (hr : 0 < r) (hcx : c ≤ x - r) (hxd : x ≤ d)
    (hE : E Θ (|ℓ| + 1) r ≤ 1) (hℓ : slope u (x - r) x ≤ ℓ) :
    ∀ ρ ∈ Ioc 0 r, slope u (x - ρ) x ≤ ℓ + E Θ (|ℓ| + 1) r := by
  intro ρ hρ
  have hE' : E Θ (|-ℓ| + 1) r ≤ 1 := by rwa [abs_neg]
  have hℓ' : -ℓ ≤ slope (fun y => u (c + d - y)) (c + d - x) (c + d - x + r) := by
    rw [slope_reflect u c d x r]
    linarith
  have key := hF.reflect.slope_mono_right hr (by linarith) (by linarith) hE' hℓ' ρ hρ
  rw [slope_reflect u c d x ρ, abs_neg] at key
  linarith

/-! ## Lemme 3.3 : dérivées unilatérales et absence de coin convexe -/

/-- **Lemme 3.3 (i)**, à droite : `u'₊(x)` existe dans `[-∞,∞]`. -/
lemma LowerFrame.exists_right_deriv (hF : LowerFrame u c d Θ) {x : ℝ} (hx : x ∈ Ico c d) :
    ∃ p : EReal,
      Tendsto (fun ρ => ((slope u x (x + ρ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 p) := by
  set φ : ℝ → EReal := fun ρ => ((slope u x (x + ρ) : ℝ) : EReal) with hφ
  refine ⟨limsup φ (𝓝[>] 0), ?_⟩
  apply tendsto_of_le_liminf_of_limsup_le _ le_rfl
  -- il suffit de montrer limsup φ ≤ liminf φ ; sinon on choisit liminf < ℓ' < ℓ < limsup
  by_contra hcon
  push Not at hcon
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
  obtain ⟨ℓ', hℓ'1, hℓ'2⟩ := EReal.lt_iff_exists_real_btwn.mp hℓ1
  have hℓℓ' : ℓ' < ℓ := EReal.coe_lt_coe_iff.mp hℓ'2
  -- φ(r) > ℓ pour des r arbitrairement petits
  have hfreq : ∃ᶠ ρ in 𝓝[>] (0 : ℝ), (ℓ : EReal) < φ ρ :=
    frequently_lt_of_lt_limsup (h := hℓ2)
  -- pour r petit : E(|ℓ|+1, r) < min(1, ℓ - ℓ'), x + r < d et r > 0
  have hEv : ∀ᶠ r in 𝓝[>] (0 : ℝ), E Θ (|ℓ| + 1) r < min 1 (ℓ - ℓ') :=
    (hF.E_tendsto_zero (|ℓ| + 1)).eventually_lt_const (lt_min one_pos (by linarith))
  have hdx : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < d - x :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by linarith [hx.2]))
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := (hfreq.and_eventually (hEv.and (hdx.and hpos))).exists
  have hℓr : ℓ ≤ slope u x (x + r) := (EReal.coe_lt_coe_iff.mp hr1).le
  -- le Lemme 3.2 (a) donne φ ≥ ℓ - E ≥ ℓ' sur ]0, r]
  have hmono := hF.slope_mono_right hr4 hx.1 (by linarith)
    (by linarith [min_le_left 1 (ℓ - ℓ')]) hℓr
  have hev2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (ℓ' : EReal) ≤ φ ρ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds hr4)]
      with ρ hρ1 hρ2
    have h1 := hmono ρ ⟨hρ1, hρ2.le⟩
    have h2 : E Θ (|ℓ| + 1) r ≤ ℓ - ℓ' := by linarith [min_le_right 1 (ℓ - ℓ')]
    show (ℓ' : EReal) ≤ ((slope u x (x + ρ) : ℝ) : EReal)
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  -- donc liminf φ ≥ ℓ', contradiction
  have h3 : (ℓ' : EReal) ≤ liminf φ (𝓝[>] 0) := le_liminf_of_le (h := hev2)
  exact absurd hℓ'1 (not_lt.mpr h3)

/-- **Lemme 3.3 (i)**, à gauche : `u'₋(x)` existe dans `[-∞,∞]` (symétrie (S₂)). -/
lemma LowerFrame.exists_left_deriv (hF : LowerFrame u c d Θ) {x : ℝ} (hx : x ∈ Ioc c d) :
    ∃ q : EReal,
      Tendsto (fun ρ => ((slope u (x - ρ) x : ℝ) : EReal)) (𝓝[>] 0) (𝓝 q) := by
  obtain ⟨p, hp⟩ := hF.reflect.exists_right_deriv (x := c + d - x)
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  refine ⟨-p, ?_⟩
  have h := (continuous_neg.tendsto p).comp hp
  simp only [Function.comp_def, slope_reflect u c d x, EReal.coe_neg, neg_neg] at h
  exact h

/-- Extraction d'un intervalle `]0, r[` à partir d'une propriété vraie près de `0⁺`. -/
lemma exists_pos_of_eventually {P : ℝ → Prop} (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), P t) :
    ∃ r > 0, ∀ t, 0 < t → t < r → P t := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨r, hr, H⟩ := h
  refine ⟨r, hr, fun t ht htr => H ?_ ht⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos ht]
  exact htr

/-- Pentes et symétrie `y ↦ c + d - y`, côté gauche : `k_ũ(x̃-ρ, x̃) = -k_u(x, x+ρ)`. -/
lemma slope_reflect' (u : ℝ → ℝ) (c d x ρ : ℝ) :
    slope (fun y => u (c + d - y)) (c + d - x - ρ) (c + d - x) = - slope u x (x + ρ) := by
  rw [slope_def_field, slope_def_field]
  have e1 : c + d - (c + d - x - ρ) = x + ρ := by ring
  have e2 : c + d - (c + d - x) = x := by ring
  simp only [e1, e2]
  have e3 : c + d - x - (c + d - x - ρ) = ρ := by ring
  have e4 : x + ρ - x = ρ := by ring
  rw [e3, e4]
  ring

/-- **Lemme 3.3 (ii), cas 1** : dérivées unilatérales finies. -/
lemma LowerFrame.no_convex_corner_finite (hF : LowerFrame u c d Θ) {x : ℝ} (hx : x ∈ Ioo c d)
    {p q : ℝ}
    (hp : Tendsto (fun ρ => slope u x (x + ρ)) (𝓝[>] 0) (𝓝 p))
    (hq : Tendsto (fun ρ => slope u (x - ρ) x) (𝓝[>] 0) (𝓝 q)) :
    p ≤ q := by
  by_contra hlt
  push Not at hlt
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = (p - q) / 4 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; linarith
  obtain ⟨K, hK⟩ : ∃ K, K = |p| + |q| + 1 := ⟨_, rfl⟩
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  -- un ε > 0 avec Θ(K, ε) < δ/2
  obtain ⟨ε, hε1, hε2⟩ :=
    (((hF.theta_tendsto_zero K).eventually_lt_const (show (0 : ℝ) < δ / 2 by linarith)).and
      hpos).exists
  have hε1' : Θ K ε < δ / 2 := hε1
  -- pour h petit : pentes proches de p et q, et [x - h, x + h] ⊂ [c, d]
  have hR := hp.eventually (Ioo_mem_nhds (show p - δ < p by linarith) (show p < p + δ by linarith))
  have hL := hq.eventually (Ioo_mem_nhds (show q - δ < q by linarith) (show q < q + δ by linarith))
  have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < min (ε / 2) (min (x - c) (d - x)) :=
    nhdsWithin_le_nhds (eventually_lt_nhds
      (lt_min (by linarith) (lt_min (by linarith [hx.1]) (by linarith [hx.2]))))
  obtain ⟨h, hRh, hLh, hsh, hh⟩ := (hR.and (hL.and (hsmall.and hpos))).exists
  have hRh' : p - δ < slope u x (x + h) ∧ slope u x (x + h) < p + δ := hRh
  have hLh' : q - δ < slope u (x - h) x ∧ slope u (x - h) x < q + δ := hLh
  have hm1 := min_le_left (ε / 2) (min (x - c) (d - x))
  have hm2 := min_le_right (ε / 2) (min (x - c) (d - x))
  have hm3 := min_le_left (x - c) (d - x)
  have hm4 := min_le_right (x - c) (d - x)
  -- le Lemme 3.1 (c) avec h' = h
  have key := hF.approx_concave_center (x := x) hh hh (by linarith) (by linarith)
  have e : h * h / (h + h) = h / 2 := by
    rw [div_eq_iff (show h + h ≠ 0 by positivity)]
    ring
  rw [min_self, e] at key
  -- la pente de la corde sur [x - h, x + h] est la moyenne des deux pentes
  have hK1 : (x + h - (x - h)) * slope u (x - h) (x + h) = u (x + h) - u (x - h) := by
    simpa using sub_smul_slope u (x - h) (x + h)
  have hR1 : (x + h - x) * slope u x (x + h) = u (x + h) - u x := by
    simpa using sub_smul_slope u x (x + h)
  have hL1 : (x - (x - h)) * slope u (x - h) x = u x - u (x - h) := by
    simpa using sub_smul_slope u (x - h) x
  have e1 : x + h - (x - h) = h + h := by ring
  have e2 : x + h - x = h := by ring
  have e3 : x - (x - h) = h := by ring
  rw [e1] at hK1
  rw [e2] at hR1
  rw [e3] at hL1
  have hmid : slope u (x - h) (x + h) = (slope u x (x + h) + slope u (x - h) x) / 2 := by
    apply mul_left_cancel₀ (show h + h ≠ 0 by positivity)
    rw [hK1]
    linear_combination -hR1 - hL1
  have habs : |slope u (x - h) (x + h)| ≤ K := by
    rw [hmid, abs_le]
    constructor <;> linarith [hRh'.1, hRh'.2, hLh'.1, hLh'.2, neg_abs_le p, le_abs_self p,
      neg_abs_le q, le_abs_self q]
  -- majoration du membre de droite
  have hsq : Real.sqrt ((h + h) * h) ≤ 2 * h := by
    calc Real.sqrt ((h + h) * h) ≤ Real.sqrt ((2 * h) ^ 2) :=
          Real.sqrt_le_sqrt (by linarith [sq_nonneg h])
      _ = 2 * h := Real.sqrt_sq (by linarith)
  have hΘ : Θ |slope u (x - h) (x + h)| (h + h) ≤ Θ K ε :=
    hF.mono _ _ _ _ habs (by linarith)
  have h5 := mul_le_mul hΘ hsq (Real.sqrt_nonneg _) (hF.nonneg _ _)
  have h6 := mul_lt_mul_of_pos_right hε1' (show (0 : ℝ) < 2 * h by linarith)
  have h7 := mul_pos hh (show 0 < slope u x (x + h) - slope u (x - h) x - 2 * δ by
    linarith [hRh'.1, hLh'.2])
  linarith

/-- **Lemme 3.3 (ii), cas 2** : `u'₊(x) = +∞` et `u'₋(x) < +∞` est impossible. -/
lemma LowerFrame.no_convex_corner_top (hF : LowerFrame u c d Θ) {x : ℝ} (hx : x ∈ Ioo c d)
    {q : EReal} (hq_lt : q < ⊤)
    (hp : Tendsto (fun ρ => ((slope u x (x + ρ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤))
    (hq : Tendsto (fun ρ => ((slope u (x - ρ) x : ℝ) : EReal)) (𝓝[>] 0) (𝓝 q)) :
    False := by
  have hpos : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ := self_mem_nhdsWithin
  -- relations « longueur × pente = accroissement »
  have hRrel : ∀ t, t * slope u x (x + t) = u (x + t) - u x := fun t => by
    simpa using sub_smul_slope u x (x + t)
  have hLrel : ∀ t, t * slope u (x - t) x = u x - u (x - t) := fun t => by
    simpa using sub_smul_slope u (x - t) x
  -- continuité de t ↦ u(x ± t) - u(x)
  have hcontR : ∀ r, r ≤ d - x → ContinuousOn (fun t => u (x + t) - u x) (Icc 0 r) := by
    intro r hr
    have hmaps : MapsTo (fun t : ℝ => x + t) (Icc 0 r) (Icc c d) := fun t ht => by
      simp only [mem_Icc]
      constructor <;> linarith [ht.1, ht.2, hx.1]
    exact (hF.cont.comp (by fun_prop) hmaps).sub continuousOn_const
  have hcontL : ∀ r, r ≤ x - c → ContinuousOn (fun t => u (x - t) - u x) (Icc 0 r) := by
    intro r hr
    have hmaps : MapsTo (fun t : ℝ => x - t) (Icc 0 r) (Icc c d) := fun t ht => by
      simp only [mem_Icc]
      constructor <;> linarith [ht.1, ht.2, hx.2]
    exact (hF.cont.comp (by fun_prop) hmaps).sub continuousOn_const
  -- M₁ ≥ 1 avec k_L < M₁ près de 0, et k_R → +∞
  obtain ⟨m, hm1, -⟩ := EReal.lt_iff_exists_real_btwn.mp hq_lt
  obtain ⟨M₁, hM₁⟩ : ∃ M₁, M₁ = max m 1 := ⟨_, rfl⟩
  have hM₁1 : 1 ≤ M₁ := by rw [hM₁]; exact le_max_right _ _
  have hmM : m ≤ M₁ := by rw [hM₁]; exact le_max_left _ _
  have hLev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), slope u (x - ρ) x < M₁ := by
    filter_upwards [hq.eventually_lt_const hm1] with ρ hρ
    have := EReal.coe_lt_coe_iff.mp hρ
    linarith
  have hRev : ∀ T : ℝ, ∀ᶠ ρ in 𝓝[>] (0 : ℝ), T < slope u x (x + ρ) := fun T => by
    filter_upwards [hp.eventually_const_lt (EReal.coe_lt_top T)] with ρ hρ
    exact EReal.coe_lt_coe_iff.mp hρ
  obtain ⟨r1, hr1, H1⟩ := exists_pos_of_eventually (hRev 1)
  obtain ⟨r2, hr2, H2⟩ := exists_pos_of_eventually hLev
  obtain ⟨t0, ht0⟩ : ∃ t0, t0 = min (min r1 r2) (min (x - c) (d - x)) := ⟨_, rfl⟩
  have ht0pos : 0 < t0 := by
    rw [ht0]
    exact lt_min (lt_min hr1 hr2) (lt_min (by linarith [hx.1]) (by linarith [hx.2]))
  have ht01 : t0 ≤ r1 := by rw [ht0]; exact (min_le_left _ _).trans (min_le_left _ _)
  have ht02 : t0 ≤ r2 := by rw [ht0]; exact (min_le_left _ _).trans (min_le_right _ _)
  have ht03 : t0 ≤ x - c := by rw [ht0]; exact (min_le_right _ _).trans (min_le_left _ _)
  have ht04 : t0 ≤ d - x := by rw [ht0]; exact (min_le_right _ _).trans (min_le_right _ _)
  by_cases hcase : ∃ᶠ h in 𝓝[>] (0 : ℝ), -M₁ ≤ slope u (x - h) x
  · -- Cas 2.1 : k_L(h_n) ≥ -M₁ pour des h_n → 0
    obtain ⟨r3, hr3, H3⟩ := exists_pos_of_eventually
      ((hF.theta_tendsto_zero (1 + M₁)).eventually_lt_const (show (0 : ℝ) < 1 / 8 by norm_num))
    obtain ⟨r4, hr4, H4⟩ := exists_pos_of_eventually (hRev (2 * M₁ + 1))
    have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < min (min t0 (r3 / 2)) r4 :=
      nhdsWithin_le_nhds (eventually_lt_nhds (lt_min (lt_min ht0pos (by linarith)) hr4))
    obtain ⟨h, hLh, hsh, hh⟩ := (hcase.and_eventually (hsmall.and hpos)).exists
    have hs1 := min_le_left (min t0 (r3 / 2)) r4
    have hs2 := min_le_right (min t0 (r3 / 2)) r4
    have hs3 := min_le_left t0 (r3 / 2)
    have hs4 := min_le_right t0 (r3 / 2)
    have hht0 : h < t0 := by linarith
    -- b(h) ≥ h, donc b(h') = h pour un h' ∈ ]0, h] (valeurs intermédiaires)
    have hkRh : 1 < slope u x (x + h) := H1 h hh (by linarith)
    have hbh : h ≤ u (x + h) - u x := by
      have := mul_lt_mul_of_pos_left hkRh hh
      linarith [hRrel h]
    obtain ⟨h', hh', hbh'⟩ := intermediate_value_Icc hh.le (hcontR h (by linarith))
      (show h ∈ Icc (u (x + 0) - u x) (u (x + h) - u x) from ⟨by simp [hh.le], hbh⟩)
    have hbh'' : u (x + h') - u x = h := hbh'
    have hh'pos : 0 < h' := by
      rcases eq_or_lt_of_le hh'.1 with h0 | h0
      · rw [← h0] at hbh''
        simp at hbh''
        linarith
      · exact h0
    have hh'h : h' ≤ h := hh'.2
    -- R = k_R(h') vérifie h = h' R, et R est grand
    have hR' : h' * slope u x (x + h') = h := by rw [hRrel h', hbh'']
    have hRbig : 2 * M₁ + 1 < slope u x (x + h') := H4 h' hh'pos (by linarith)
    have hkL1 : slope u (x - h) x < M₁ := H2 h hh (by linarith)
    -- la pente de la corde sur [x - h, x + h'] est bornée par 1 + M₁
    have hK : (x + h' - (x - h)) * slope u (x - h) (x + h') = u (x + h') - u (x - h) := by
      simpa using sub_smul_slope u (x - h) (x + h')
    have e1 : x + h' - (x - h) = h + h' := by ring
    rw [e1] at hK
    have hLh' := hLrel h
    have hup : (h + h') * slope u (x - h) (x + h') ≤ (h + h') * (1 + M₁) := by
      have := mul_le_mul_of_nonneg_left hkL1.le hh.le
      have := mul_nonneg hh'pos.le (show (0 : ℝ) ≤ 1 + M₁ by linarith)
      linarith
    have hlow : (h + h') * (-(1 + M₁)) ≤ (h + h') * slope u (x - h) (x + h') := by
      have := mul_le_mul_of_nonneg_left hLh hh.le
      have := mul_nonneg hh'pos.le (show (0 : ℝ) ≤ M₁ by linarith)
      linarith
    have habs : |slope u (x - h) (x + h')| ≤ 1 + M₁ := by
      rw [abs_le]
      exact ⟨le_of_mul_le_mul_left hlow (by linarith), le_of_mul_le_mul_left hup (by linarith)⟩
    -- le Lemme 3.1 (c)
    have key := hF.approx_concave_center (x := x) hh hh'pos (by linarith) (by linarith)
    rw [min_eq_right hh'h] at key
    have hsq : Real.sqrt ((h + h') * h') ≤ 2 * h := by
      have i1 := mul_le_mul_of_nonneg_left hh'h hh'pos.le
      have i2 := mul_le_mul_of_nonneg_left hh'h hh.le
      calc Real.sqrt ((h + h') * h') ≤ Real.sqrt ((2 * h) ^ 2) :=
            Real.sqrt_le_sqrt (by linarith [sq_nonneg h])
        _ = 2 * h := Real.sqrt_sq (by linarith)
    have hΘ : Θ |slope u (x - h) (x + h')| (h + h') ≤ Θ (1 + M₁) (2 * h) :=
      hF.mono _ _ _ _ habs (by linarith)
    have hΘsmall : Θ (1 + M₁) (2 * h) < 1 / 8 := H3 (2 * h) (by linarith) (by linarith)
    have hA : h' / 2 ≤ h * h' / (h + h') := by
      rw [le_div_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left hh'h hh'pos.le
      linarith
    have hD : 0 ≤ slope u x (x + h') - slope u (x - h) x := by linarith
    have s1 := mul_le_mul_of_nonneg_right hA hD
    have s2 := mul_le_mul hΘ hsq (Real.sqrt_nonneg _) (hF.nonneg _ _)
    have s3 := mul_lt_mul_of_pos_right hΘsmall (show (0 : ℝ) < 2 * h by linarith)
    have s4 := mul_pos hh'pos (show 0 < slope u x (x + h') / 4 - slope u (x - h) x / 2 by
      linarith)
    linarith
  · -- Cas 2.2 : k_L < -M₁ près de 0
    simp only [Filter.not_frequently, not_le] at hcase
    obtain ⟨r5, hr5, H5⟩ := exists_pos_of_eventually hcase
    obtain ⟨r6, hr6, H6⟩ := exists_pos_of_eventually
      ((hF.theta_tendsto_zero 0).eventually_lt_const (show (0 : ℝ) < 1 / 4 by norm_num))
    obtain ⟨β, hβ⟩ : ∃ β, β = min (min t0 r5) (r6 / 2) / 2 := ⟨_, rfl⟩
    have hb1 := min_le_left (min t0 r5) (r6 / 2)
    have hb2 := min_le_right (min t0 r5) (r6 / 2)
    have hb3 := min_le_left t0 r5
    have hb4 := min_le_right t0 r5
    have hmpos : 0 < min (min t0 r5) (r6 / 2) := lt_min (lt_min ht0pos hr5) (by linarith)
    have hβpos : 0 < β := by rw [hβ]; linarith
    have hβm : β < min (min t0 r5) (r6 / 2) := by rw [hβ]; linarith
    -- a(β) > β et b(β) > β
    have hkLβ : slope u (x - β) x < -M₁ := H5 β hβpos (by linarith)
    have hkRβ : 1 < slope u x (x + β) := H1 β hβpos (by linarith)
    have haβ : β ≤ u (x - β) - u x := by
      have := mul_lt_mul_of_pos_left hkLβ hβpos
      have := mul_le_mul_of_nonneg_left hM₁1 hβpos.le
      linarith [hLrel β]
    have hbβ : β ≤ u (x + β) - u x := by
      have := mul_lt_mul_of_pos_left hkRβ hβpos
      linarith [hRrel β]
    -- valeurs intermédiaires : a(h) = β et b(h') = β avec h, h' ∈ ]0, β]
    obtain ⟨h, hh, hah⟩ := intermediate_value_Icc hβpos.le (hcontL β (by linarith))
      (show β ∈ Icc (u (x - 0) - u x) (u (x - β) - u x) from ⟨by simp [hβpos.le], haβ⟩)
    obtain ⟨h', hh', hbh⟩ := intermediate_value_Icc hβpos.le (hcontR β (by linarith))
      (show β ∈ Icc (u (x + 0) - u x) (u (x + β) - u x) from ⟨by simp [hβpos.le], hbβ⟩)
    have hah' : u (x - h) - u x = β := hah
    have hbh' : u (x + h') - u x = β := hbh
    have hhpos : 0 < h := by
      rcases eq_or_lt_of_le hh.1 with h0 | h0
      · rw [← h0] at hah'
        simp at hah'
        linarith
      · exact h0
    have hh'pos : 0 < h' := by
      rcases eq_or_lt_of_le hh'.1 with h0 | h0
      · rw [← h0] at hbh'
        simp at hbh'
        linarith
      · exact h0
    -- la corde sur [x - h, x + h'] est horizontale
    have hK : (x + h' - (x - h)) * slope u (x - h) (x + h') = u (x + h') - u (x - h) := by
      simpa using sub_smul_slope u (x - h) (x + h')
    have e1 : x + h' - (x - h) = h + h' := by ring
    rw [e1] at hK
    have hslope0 : slope u (x - h) (x + h') = 0 := by
      have h00 : (h + h') * slope u (x - h) (x + h') = 0 := by rw [hK]; linarith
      exact (mul_eq_zero.mp h00).resolve_left (ne_of_gt (by linarith))
    -- l'inégalité (3.1) aux points x - h < x < x + h'
    have h0 := hF.approx_concave (show c ≤ x - h by linarith [hh.2])
      (show x - h < x by linarith) (show x < x + h' by linarith)
      (show x + h' ≤ d by linarith [hh'.2])
    have e2 : x - (x - h) = h := by ring
    have e3 : x + h' - x = h' := by ring
    rw [hslope0, abs_zero, e1, e2, e3] at h0
    have hmin : min h h' ≤ β := (min_le_left h h').trans hh.2
    have hminpos : 0 ≤ min h h' := le_min hhpos.le hh'pos.le
    have hsq : Real.sqrt ((h + h') * min h h') ≤ 2 * β := by
      have i1 := mul_le_mul (show h + h' ≤ 2 * β by linarith [hh.2, hh'.2]) hmin hminpos
        (by linarith)
      calc Real.sqrt ((h + h') * min h h') ≤ Real.sqrt ((2 * β) ^ 2) :=
            Real.sqrt_le_sqrt (by linarith [sq_nonneg β])
        _ = 2 * β := Real.sqrt_sq (by linarith)
    have hΘ : Θ 0 (h + h') ≤ Θ 0 (2 * β) :=
      hF.mono _ _ _ _ le_rfl (by linarith [hh.2, hh'.2])
    have hΘsmall : Θ 0 (2 * β) < 1 / 4 := H6 (2 * β) (by linarith) (by linarith)
    have s1 := mul_le_mul hΘ hsq (Real.sqrt_nonneg _) (hF.nonneg _ _)
    have s2 := mul_lt_mul_of_pos_right hΘsmall (show (0 : ℝ) < 2 * β by linarith)
    linarith

/-- **Lemme 3.3 (ii)** : pas de coin convexe, `u'₊(x) ≤ u'₋(x)`. -/
lemma LowerFrame.no_convex_corner (hF : LowerFrame u c d Θ) {x : ℝ} (hx : x ∈ Ioo c d)
    {p q : EReal}
    (hp : Tendsto (fun ρ => ((slope u x (x + ρ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 p))
    (hq : Tendsto (fun ρ => ((slope u (x - ρ) x : ℝ) : EReal)) (𝓝[>] 0) (𝓝 q)) :
    p ≤ q := by
  by_contra hlt
  push Not at hlt
  induction p using EReal.rec with
  | bot => exact not_lt_bot hlt
  | top => exact hF.no_convex_corner_top hx hlt hp hq
  | coe p' =>
    induction q using EReal.rec with
    | top => exact not_top_lt hlt
    | coe q' =>
      exact absurd (hF.no_convex_corner_finite hx (EReal.tendsto_coe.mp hp)
        (EReal.tendsto_coe.mp hq)) (not_le.mpr (EReal.coe_lt_coe_iff.mp hlt))
    | bot =>
      -- symétrie (S₂) : on se ramène au cas 2 pour ũ = u(c + d - ·) en c + d - x
      have hp' : Tendsto (fun ρ => ((slope (fun y => u (c + d - y)) (c + d - x)
          (c + d - x + ρ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ⊤) := by
        simp only [slope_reflect u c d x, EReal.coe_neg]
        have := (continuous_neg.tendsto (⊥ : EReal)).comp hq
        rw [EReal.neg_bot] at this
        exact this
      have hq' : Tendsto (fun ρ => ((slope (fun y => u (c + d - y)) (c + d - x - ρ)
          (c + d - x) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (-(p' : EReal))) := by
        simp only [slope_reflect' u c d x, EReal.coe_neg]
        exact (continuous_neg.tendsto _).comp hp
      have hlt' : -(p' : EReal) < ⊤ := by
        rw [← EReal.coe_neg]
        exact EReal.coe_lt_top _
      exact hF.reflect.no_convex_corner_top (x := c + d - x)
        ⟨by linarith [hx.2], by linarith [hx.1]⟩ hlt' hp' hq'

end TonelliObstacle
