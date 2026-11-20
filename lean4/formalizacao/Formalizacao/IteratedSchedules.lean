import Formalizacao.RegularSchedules

/-!
# Séries de Bertrand para qualquer número de logaritmos (Observação 6.13)

Cada condensação de Cauchy remove um fator e troca `1 + log(2^k)` por `k + 1`,
até constantes. Ao fim sobra uma série de potências.
-/

open scoped ENNReal
open Set FormalizacaoLow FormalizacaoLp FormalizacaoRegular

namespace FormalizacaoIterated

/-- Passo da iteração logarítmica. -/
noncomputable def nextLog (x : ℝ) : ℝ := 1 + Real.log x

private lemma nextLog_ge {x : ℝ} (hx : 1 ≤ x) : 1 ≤ nextLog x :=
  le_add_of_nonneg_right (Real.log_nonneg hx)

private lemma nextLog_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) : nextLog x ≤ nextLog y :=
  add_le_add_right (Real.log_le_log (zero_lt_one.trans_le hx) hxy) _

private lemma nextLog_le_mul {C x y : ℝ} (hC : 1 ≤ C) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxy : x ≤ C * y) : nextLog x ≤ nextLog C * nextLog y := by
  have hl := Real.log_le_log (zero_lt_one.trans_le hx) hxy
  rw [Real.log_mul (by positivity) (by positivity)] at hl
  have hC₀ := Real.log_nonneg hC
  have hy₀ := Real.log_nonneg hy
  unfold nextLog
  nlinarith [mul_nonneg hC₀ hy₀]

/-- Denominador com `m` fatores de expoente um, seguido de uma potência de expoente `a`. -/
noncomputable def bertrandDen (a : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x ^ a
  | m + 1, x => x * bertrandDen a m (nextLog x)

private lemma bertrandDen_ge {a : ℝ} (ha : 0 ≤ a) (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ bertrandDen a m x := by
  induction m generalizing x with
  | zero => exact Real.one_le_rpow hx ha
  | succ m ih => exact one_le_mul_of_one_le_of_one_le hx (ih (nextLog_ge hx))

private lemma bertrandDen_mono {a : ℝ} (ha : 0 ≤ a) (m : ℕ) {x y : ℝ}
    (hx : 1 ≤ x) (hxy : x ≤ y) : bertrandDen a m x ≤ bertrandDen a m y := by
  induction m generalizing x y with
  | zero => exact Real.rpow_le_rpow (zero_le_one.trans hx) hxy ha
  | succ m ih =>
    exact mul_le_mul hxy (ih (nextLog_ge hx) (nextLog_mono hx hxy))
      (zero_le_one.trans (bertrandDen_ge ha m (nextLog_ge hx))) (zero_le_one.trans (hx.trans hxy))

private lemma bertrandDen_scale {a : ℝ} (ha : 0 ≤ a) (m : ℕ) {C : ℝ} (hC : 1 ≤ C) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → x ≤ C * y →
      bertrandDen a m x ≤ D * bertrandDen a m y := by
  induction m generalizing C with
  | zero =>
    refine ⟨C ^ a, Real.one_le_rpow hC ha, fun x y hx hy hxy ↦ ?_⟩
    simp only [bertrandDen]
    refine (Real.rpow_le_rpow (zero_le_one.trans hx) hxy ha).trans_eq ?_
    rw [Real.mul_rpow (zero_le_one.trans hC) (zero_le_one.trans hy)]
  | succ m ih =>
    obtain ⟨D, hD, hd⟩ := ih (nextLog_ge hC)
    refine ⟨C * D, one_le_mul_of_one_le_of_one_le hC hD, fun x y hx hy hxy ↦ ?_⟩
    have h := hd _ _ (nextLog_ge hx) (nextLog_ge hy) (nextLog_le_mul hC hx hy hxy)
    simp only [bertrandDen]
    calc _ ≤ (C * y) * (D * bertrandDen a m (nextLog y)) :=
          mul_le_mul hxy h (zero_le_one.trans (bertrandDen_ge ha m (nextLog_ge hx))) (by positivity)
      _ = _ := by ring

private lemma summable_bertrand_compare {a : ℝ} (ha : 0 ≤ a) (m : ℕ) {x y : ℕ → ℝ}
    (hx : ∀ k, 1 ≤ x k) (hy : ∀ k, 1 ≤ y k)
    (hxy : ∀ k, x k ≤ 2 * y k) (hyx : ∀ k, y k ≤ 2 * x k) :
    Summable (fun k ↦ 1 / bertrandDen a m (x k)) ↔
      Summable (fun k ↦ 1 / bertrandDen a m (y k)) := by
  obtain ⟨D, hD, hd⟩ := bertrandDen_scale ha m (C := 2) (by norm_num)
  have hp (x : ℝ) (hx : 1 ≤ x) := zero_lt_one.trans_le (bertrandDen_ge ha m hx)
  apply summable_iff_of_comparable (C := D) (D := D)
    (fun k ↦ div_nonneg zero_le_one (hp _ (hx k)).le)
    (fun k ↦ div_nonneg zero_le_one (hp _ (hy k)).le)
  · intro k
    rw [mul_one_div, div_le_div_iff₀ (hp _ (hx k)) (hp _ (hy k)), one_mul]
    exact hd _ _ (hy k) (hx k) (hyx k)
  · intro k
    rw [mul_one_div, div_le_div_iff₀ (hp _ (hy k)) (hp _ (hx k)), one_mul]
    exact hd _ _ (hx k) (hy k) (hxy k)

set_option maxHeartbeats 500000 in
/-- A série de Bertrand converge se e somente se o último expoente é maior que um. -/
theorem bertrand_summable_iff {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    Summable (fun k : ℕ ↦ 1 / bertrandDen a m ((k : ℝ) + 1)) ↔ 1 < a := by
  induction m with
  | zero =>
    simpa only [bertrandDen, Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun k : ℕ ↦ 1 / (k : ℝ) ^ a) 1).trans
        Real.summable_one_div_nat_rpow
  | succ m ih =>
    let f (k : ℕ) := 1 / bertrandDen a (m + 1) (k : ℝ)
    have hf (k : ℕ) : 0 ≤ f k := by
      cases k with
      | zero => simp [f, bertrandDen]
      | succ k =>
        exact div_nonneg zero_le_one
          (zero_le_one.trans (bertrandDen_ge ha _ (by exact_mod_cast Nat.le_add_left 1 k)))
    have hfm ⦃k l : ℕ⦄ (hk : 0 < k) (hkl : k ≤ l) : f l ≤ f k :=
      one_div_le_one_div_of_le
        (zero_lt_one.trans_le (bertrandDen_ge ha _ (by exact_mod_cast hk)))
        (bertrandDen_mono ha _ (by exact_mod_cast hk) (by exact_mod_cast hkl))
    have hc := summable_condensed_iff_of_nonneg hf hfm
    have he (k : ℕ) : (2 : ℝ) ^ k * f (2 ^ k) =
        1 / bertrandDen a m (nextLog ((2 : ℝ) ^ k)) := by
      simp only [f, bertrandDen, Nat.cast_pow, Nat.cast_ofNat]
      field_simp
    simp_rw [he] at hc
    have h (k : ℕ) : nextLog ((2 : ℝ) ^ k) = 1 + (k : ℝ) * Real.log 2 := by
      rw [nextLog, Real.log_pow]
    have hcmp := summable_bertrand_compare ha m
      (x := fun k ↦ nextLog ((2 : ℝ) ^ k)) (y := fun k ↦ (k : ℝ) + 1)
      (fun _ ↦ nextLog_ge (one_le_pow₀ (by norm_num)))
      (fun k ↦ le_add_of_nonneg_left (Nat.cast_nonneg k))
      (fun k ↦ by dsimp; rw [h]; nlinarith [Real.log_two_lt_d9, Nat.cast_nonneg (α := ℝ) k])
      (fun k ↦ by dsimp; rw [h]; nlinarith [Real.log_two_gt_d9, Nat.cast_nonneg (α := ℝ) k])
    have hshift : (fun k : ℕ ↦ 1 / bertrandDen a (m + 1) ((k : ℝ) + 1)) =
        (fun k : ℕ ↦ f (k + 1)) := by
      funext k
      simp only [f, Nat.cast_add, Nat.cast_one]
    rw [hshift]
    exact ((summable_nat_add_iff (f := f) 1).trans hc.symm).trans (hcmp.trans ih)

/-- Fator com `m` logaritmos de expoente `1/q`, seguidos do último de expoente `γ`.
O argumento real é o primeiro logaritmo da agenda. -/
noncomputable def iteratedFactor (q : ℝ≥0∞) (γ : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x ^ γ
  | m + 1, x => x ^ q.toReal⁻¹ * iteratedFactor q γ m (nextLog x)

lemma iteratedFactor_ge (q : ℝ≥0∞) {γ : ℝ} (hγ : 0 ≤ γ) (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ iteratedFactor q γ m x := by
  induction m generalizing x with
  | zero => exact Real.one_le_rpow hx hγ
  | succ m ih =>
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow hx (inv_nonneg.mpr ENNReal.toReal_nonneg)) (ih (nextLog_ge hx))

lemma iteratedFactor_mono (q : ℝ≥0∞) {γ : ℝ} (hγ : 0 ≤ γ) (m : ℕ) {x y : ℝ}
    (hx : 1 ≤ x) (hxy : x ≤ y) : iteratedFactor q γ m x ≤ iteratedFactor q γ m y := by
  induction m generalizing x y with
  | zero => exact Real.rpow_le_rpow (zero_le_one.trans hx) hxy hγ
  | succ m ih =>
    exact mul_le_mul (Real.rpow_le_rpow (zero_le_one.trans hx) hxy
      (inv_nonneg.mpr ENNReal.toReal_nonneg)) (ih (nextLog_ge hx) (nextLog_mono hx hxy))
      (zero_le_one.trans (iteratedFactor_ge q hγ m (nextLog_ge hx)))
      (Real.rpow_nonneg (zero_le_one.trans (hx.trans hxy)) _)

private lemma iteratedFactor_pow {q : ℝ≥0∞} (hqR : 0 < q.toReal) {γ : ℝ} (hγ : 0 ≤ γ)
    (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    iteratedFactor q γ m x ^ q.toReal = bertrandDen (γ * q.toReal) m x := by
  induction m generalizing x with
  | zero => exact (Real.rpow_mul (zero_le_one.trans hx) _ _).symm
  | succ m ih =>
    have hx₀ := zero_le_one.trans hx
    simp only [iteratedFactor, bertrandDen]
    rw [Real.mul_rpow (Real.rpow_nonneg hx₀ _) (zero_le_one.trans
      (iteratedFactor_ge q hγ m (nextLog_ge hx))), ← Real.rpow_mul hx₀,
      inv_mul_cancel₀ hqR.ne', Real.rpow_one, ih (nextLog_ge hx)]

/-- Fator da agenda diádica com `m + 1` logaritmos. -/
theorem iterated_factor_summable_iff {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤)
    {γ : ℝ} (hγ : 0 ≤ γ) (m : ℕ) :
    Summable (fun k : ℕ ↦ iteratedFactor q γ m (Lfun (2 ^ (k + 1))) ^ (-q.toReal)) ↔
      1 < γ * q.toReal := by
  have hqR := ENNReal.toReal_pos hq.ne' hqt
  have he (k : ℕ) : iteratedFactor q γ m (Lfun (2 ^ (k + 1))) ^ (-q.toReal) =
      1 / bertrandDen (γ * q.toReal) m (Lfun (2 ^ (k + 1))) := by
    have hL := one_le_Lfun (N := 2 ^ (k + 1)) Nat.one_le_two_pow
    rw [Real.rpow_neg (zero_le_one.trans (iteratedFactor_ge q hγ m hL)),
      iteratedFactor_pow hqR hγ m hL, one_div]
  simp_rw [he]
  have ha := mul_nonneg hγ hqR.le
  have hcmp := summable_bertrand_compare ha m
    (x := fun k ↦ Lfun (2 ^ (k + 1))) (y := fun k ↦ (k : ℝ) + 1)
    (fun _ ↦ one_le_Lfun Nat.one_le_two_pow) (fun k ↦ le_add_of_nonneg_left (Nat.cast_nonneg k))
    (fun k ↦ by dsimp; rw [Lfun_two_pow]; push_cast
                nlinarith [Real.log_two_lt_d9, Nat.cast_nonneg (α := ℝ) k])
    (fun k ↦ by dsimp; rw [Lfun_two_pow]; push_cast
                nlinarith [Real.log_two_gt_d9, Nat.cast_nonneg (α := ℝ) k])
  exact hcmp.trans (bertrand_summable_iff ha m)

/-- Critério de somabilidade para a agenda com `m + 1` logaritmos. -/
theorem iterated_schedule_iff {s : ℝ} (hs : 1 ≤ s) {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤)
    {γ : ℝ} (hγ : 0 ≤ γ) (m : ℕ) :
    lqNorm q (scheduleWeight s (Hregular s (fun N ↦ iteratedFactor q γ m (Lfun N)))) < ⊤ ↔
      1 < γ * q.toReal := by
  have h := regular_schedule_criterion hs hq hqt
    (h := fun N ↦ iteratedFactor q γ m (Lfun N))
    (fun _ hN ↦ iteratedFactor_ge q hγ m (one_le_Lfun hN))
    (fun _ hN _ hM hNM ↦ iteratedFactor_mono q hγ m (one_le_Lfun hN) (Lfun_mono hN hM hNM))
  exact h.1.trans (iterated_factor_summable_iff hq hqt hγ m)

end FormalizacaoIterated
