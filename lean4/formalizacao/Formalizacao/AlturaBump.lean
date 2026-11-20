import Formalizacao.ArithmeticFloor

/-!
# Funções-teste suaves e cotas de Besov (auditoria, Parte II, Lema 2.1 do relatório)

Para uma função `φ` fixa, de classe `C^2`, com suporte em `(0,1)`, e para `a, t > 0`,
`f(x) = a φ((x - x₀)/t)`. Demonstramos:

* `|Δ²_h f| ≤ a M (h/t)²` e `Δ²_h f = 0` fora de `U = I ∪ (I-h) ∪ (I-2h)`, com `I = (x₀, x₀+t)`;
* `|Δ²_h f| ≤ 4 a C₀` (com `C₀ = sup|φ|`), de modo que `‖Δ²_h f‖_p ≤ 3^{1/p} t^{1/p} · min{4C₀, M(h/t)²}`;
* `ω_p(f,τ) ≤ K a t^{1/p} min{1,(τ/t)²}` com `K = max{4C₀, M}`.

Os constantes são explícitas; nenhum resultado depende de `sorry`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace FormalizacaoAltura

open FormalizacaoLp

/-! ## Diferenças de segunda ordem de uma função `C^2` -/

/-- Lipschitz da derivada: se `|φ''| ≤ M`, então `|φ'(b) - φ'(a)| ≤ M |b - a|`. -/
lemma deriv_lip {φ : ℝ → ℝ} (hφ' : Differentiable ℝ (deriv φ)) {M : ℝ}
    (hbd : ∀ z, |deriv (deriv φ) z| ≤ M) (a b : ℝ) :
    |deriv φ b - deriv φ a| ≤ M * |b - a| := by
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := deriv φ) (s := univ)
    (C := M) (fun x _ => hφ' x) (fun x _ => by simpa [Real.norm_eq_abs] using hbd x)
    convex_univ (mem_univ a) (mem_univ b)
  simpa [Real.norm_eq_abs] using key

/-- Cota da segunda diferença em escala unitária: `|φ(y+2η) - 2φ(y+η) + φ(y)| ≤ M η²`. -/
lemma diff2_unit_le {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ))
    {M : ℝ} (hbd : ∀ z, |deriv (deriv φ) z| ≤ M) (η y : ℝ) :
    |φ (y + 2 * η) - 2 * φ (y + η) + φ y| ≤ M * η ^ 2 := by
  set G : ℝ → ℝ := fun z => φ (z + η) - φ z with hG
  have hGd : ∀ z, HasDerivAt G (deriv φ (z + η) - deriv φ z) z := by
    intro z
    have h1 : HasDerivAt (fun z => φ (z + η)) (deriv φ (z + η)) z := by
      have hf := (hφ (z + η)).hasDerivAt
      have hl : HasDerivAt (fun x : ℝ => x + η) 1 z := (hasDerivAt_id z).add_const η
      simpa using hf.comp z hl
    exact h1.sub (hφ z).hasDerivAt
  have hbound : ∀ z ∈ (univ : Set ℝ), ‖deriv G z‖ ≤ M * |η| := by
    intro z _
    rw [(hGd z).deriv, Real.norm_eq_abs]
    have := deriv_lip hφ' hbd z (z + η)
    have e : z + η - z = η := by ring
    rw [e] at this
    simpa using this
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := G) (s := univ)
    (C := M * |η|) (fun x _ => (hGd x).differentiableAt) hbound convex_univ (mem_univ y)
    (mem_univ (y + η))
  have hid : G (y + η) - G y = φ (y + 2 * η) - 2 * φ (y + η) + φ y := by
    simp only [hG]
    have e : y + η + η = y + 2 * η := by ring
    rw [e]; ring
  rw [← hid]
  have hn : ‖G (y + η) - G y‖ ≤ M * |η| * |η| := by
    have := key
    simp only [Real.norm_eq_abs, add_sub_cancel_left] at this
    exact this
  rw [Real.norm_eq_abs] at hn
  calc |G (y + η) - G y| ≤ M * |η| * |η| := hn
    _ = M * η ^ 2 := by rw [mul_assoc, abs_mul_abs_self]; ring

/-! ## Escala `x ↦ a φ((x - x₀)/t)` -/

/-- A função escalada `a φ((x - x₀)/t)`. -/
noncomputable def bumpS (φ : ℝ → ℝ) (a x0 t : ℝ) : ℝ → ℝ :=
  fun x => a * φ ((x - x0) / t)

lemma diff2_bumpS {φ : ℝ → ℝ} {a x0 t : ℝ} (ht : 0 < t) (h x : ℝ) :
    diff2 h (bumpS φ a x0 t) x = a * (φ ((x - x0) / t + 2 * (h / t))
      - 2 * φ ((x - x0) / t + h / t) + φ ((x - x0) / t)) := by
  unfold diff2 bumpS
  have e1 : (x + 2 * h - x0) / t = (x - x0) / t + 2 * (h / t) := by
    field_simp; ring
  have e2 : (x + h - x0) / t = (x - x0) / t + h / t := by
    field_simp; ring
  rw [e1, e2]; ring

/-- Suporte: fora de `I ∪ (I - h) ∪ (I - 2h)`, com `I = (x₀, x₀+t)`, a segunda diferença se anula. -/
lemma diff2_bumpS_eq_zero {φ : ℝ → ℝ} (hφ0 : ∀ z, z ∉ Ioo (0 : ℝ) 1 → φ z = 0)
    {a x0 t : ℝ} (ht : 0 < t) {h : ℝ} (hh : 0 ≤ h) {x : ℝ}
    (hx : x ∉ Ioo x0 (x0 + t) ∧ x + h ∉ Ioo x0 (x0 + t) ∧ x + 2 * h ∉ Ioo x0 (x0 + t)) :
    diff2 h (bumpS φ a x0 t) x = 0 := by
  obtain ⟨h1, h2, h3⟩ := hx
  have hz : ∀ z, z ∉ Ioo x0 (x0 + t) → φ ((z - x0) / t) = 0 := by
    intro z hz
    apply hφ0
    rintro ⟨h1', h2'⟩
    apply hz
    constructor
    · have := (div_pos_iff_of_pos_right ht).mp h1'; linarith
    · have := (div_lt_one ht).mp h2'; linarith
  unfold diff2 bumpS
  simp only [hz x h1, hz (x + h) h2, hz (x + 2 * h) h3]
  ring

/-! ## Suporte, medida e normas `L^p` -/

/-- Conjunto que contém o suporte das três parcelas de `Δ²_h` para `bumpS` com suporte em `I`. -/
def supU (x0 t h : ℝ) : Set ℝ :=
  Ioo x0 (x0 + t) ∪ ((· + h) ⁻¹' Ioo x0 (x0 + t)) ∪ ((· + 2 * h) ⁻¹' Ioo x0 (x0 + t))

lemma measurableSet_supU (x0 t h : ℝ) : MeasurableSet (supU x0 t h) := by
  unfold supU
  exact ((measurableSet_Ioo).union ((measurableSet_Ioo).preimage (measurable_add_const h))).union
    ((measurableSet_Ioo).preimage (measurable_add_const (2 * h)))

lemma volume_supU_le (x0 t h : ℝ) (ht : 0 < t) :
    volume (supU x0 t h) ≤ ENNReal.ofReal (3 * t) := by
  unfold supU
  have hI : volume (Ioo x0 (x0 + t)) = ENNReal.ofReal t := by
    rw [Real.volume_Ioo]; congr 1; ring
  calc volume (Ioo x0 (x0 + t) ∪ ((· + h) ⁻¹' Ioo x0 (x0 + t)) ∪
          ((· + 2 * h) ⁻¹' Ioo x0 (x0 + t)))
      ≤ volume (Ioo x0 (x0 + t) ∪ ((· + h) ⁻¹' Ioo x0 (x0 + t))) +
          volume ((· + 2 * h) ⁻¹' Ioo x0 (x0 + t)) := measure_union_le _ _
    _ ≤ (volume (Ioo x0 (x0 + t)) + volume ((· + h) ⁻¹' Ioo x0 (x0 + t))) +
          volume ((· + 2 * h) ⁻¹' Ioo x0 (x0 + t)) := add_le_add (measure_union_le _ _) le_rfl
    _ = ENNReal.ofReal t + ENNReal.ofReal t + ENNReal.ofReal t := by
          rw [measure_preimage_add_right, measure_preimage_add_right, hI]
    _ = ENNReal.ofReal (3 * t) := by
          rw [← ENNReal.ofReal_add ht.le ht.le, ← ENNReal.ofReal_add (by positivity) ht.le]
          congr 1; ring

/-- Cota genérica em `L^p`: `|g| ≤ c 1_U` com `c ≥ 0` dá `‖g‖_p ≤ c · vol(U)^{1/p}`. -/
lemma eLpNorm_le_of_indicator {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {g : ℝ → ℝ} {U : Set ℝ}
    (hU : MeasurableSet U) {c : ℝ} (hc : 0 ≤ c) (hg : ∀ x, |g x| ≤ U.indicator (fun _ => c) x)
    (μ : Measure ℝ) (hμ : μ ≤ volume) :
    eLpNorm g p μ ≤ ENNReal.ofReal c * volume U ^ p.toReal⁻¹ := by
  classical
  rcases hc.eq_or_lt with hc0 | hcpos
  · subst hc0
    have h0 : ∀ x, |g x| ≤ 0 := fun x => by
      have := hg x
      rw [Set.indicator_apply] at this
      split_ifs at this with _ <;> simpa using this
    have hz : g = 0 := funext fun x => abs_nonpos_iff.mp (h0 x)
    simp [hz]
  · have h1 : eLpNorm g p μ ≤ eLpNorm (U.indicator (fun _ => c)) p μ :=
      eLpNorm_mono_real (fun x => by simpa [Real.norm_eq_abs] using hg x)
    have h2 : eLpNorm (U.indicator (fun _ => c)) p volume =
        ENNReal.ofReal c * volume U ^ p.toReal⁻¹ := by
      rw [eLpNorm_indicator_const hU hp0 hpt, Real.enorm_of_nonneg hc, one_div]
    exact h1.trans ((eLpNorm_mono_measure _ hμ).trans h2.le)

/-! ## Cotas pontuais e em `L^p` para `bumpS` -/

lemma abs_bumpS_le {φ : ℝ → ℝ} {C0 : ℝ} (hC0 : ∀ z, |φ z| ≤ C0) (a x0 t x : ℝ) :
    |bumpS φ a x0 t x| ≤ |a| * C0 := by
  unfold bumpS
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hC0 _) (abs_nonneg _)

lemma abs_diff2_bumpS_le_four {φ : ℝ → ℝ} {C0 : ℝ} (hC0 : ∀ z, |φ z| ≤ C0) (a x0 t h x : ℝ) :
    |diff2 h (bumpS φ a x0 t) x| ≤ 4 * (|a| * C0) := by
  have h1 := abs_le.mp (abs_bumpS_le hC0 a x0 t (x + 2 * h))
  have h2 := abs_le.mp (abs_bumpS_le hC0 a x0 t (x + h))
  have h3 := abs_le.mp (abs_bumpS_le hC0 a x0 t x)
  unfold diff2
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

lemma abs_diff2_bumpS_le_M {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ))
    {M : ℝ} (hM : ∀ z, |deriv (deriv φ) z| ≤ M) {a x0 t : ℝ} (ht : 0 < t) (h x : ℝ) :
    |diff2 h (bumpS φ a x0 t) x| ≤ |a| * M * (h / t) ^ 2 := by
  rw [diff2_bumpS ht, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (diff2_unit_le hφ hφ' hM (h / t) _) (abs_nonneg _)

/-- Cota pontual com suporte: `|Δ²_h f| ≤ min{4|a|C₀, |a| M (h/t)²}` em `U`, e `0` fora. -/
lemma abs_diff2_bumpS_le_indicator {φ : ℝ → ℝ} (hφ0 : ∀ z, z ∉ Ioo (0 : ℝ) 1 → φ z = 0)
    {C0 M : ℝ} (hC0 : ∀ z, |φ z| ≤ C0) (hφ : Differentiable ℝ φ)
    (hφ' : Differentiable ℝ (deriv φ)) (hM : ∀ z, |deriv (deriv φ) z| ≤ M) (hM0 : 0 ≤ M)
    {a x0 t : ℝ} (ht : 0 < t) {h : ℝ} (hh : 0 ≤ h) (x : ℝ) :
    |diff2 h (bumpS φ a x0 t) x| ≤
      (supU x0 t h).indicator (fun _ => min (4 * (|a| * C0)) (|a| * M * (h / t) ^ 2)) x := by
  classical
  by_cases hx : x ∈ supU x0 t h
  · rw [Set.indicator_of_mem hx]
    exact le_min (abs_diff2_bumpS_le_four hC0 a x0 t h x) (abs_diff2_bumpS_le_M hφ hφ' hM ht h x)
  · rw [Set.indicator_of_notMem hx]
    have hx' : x ∉ Ioo x0 (x0 + t) ∧ x + h ∉ Ioo x0 (x0 + t) ∧ x + 2 * h ∉ Ioo x0 (x0 + t) := by
      unfold supU at hx
      simp only [Set.mem_union, Set.mem_preimage, not_or] at hx
      exact ⟨hx.1.1, hx.1.2, hx.2⟩
    rw [diff2_bumpS_eq_zero hφ0 ht hh hx', abs_zero]

lemma bumpS_eq_zero {φ : ℝ → ℝ} (hφ0 : ∀ z, z ∉ Ioo (0 : ℝ) 1 → φ z = 0)
    {a x0 t : ℝ} (ht : 0 < t) {x : ℝ} (hx : x ∉ Ioo x0 (x0 + t)) : bumpS φ a x0 t x = 0 := by
  unfold bumpS
  have : φ ((x - x0) / t) = 0 := by
    apply hφ0
    rintro ⟨h1', h2'⟩
    apply hx
    constructor
    · have := (div_pos_iff_of_pos_right ht).mp h1'; linarith
    · have := (div_lt_one ht).mp h2'; linarith
  rw [this, mul_zero]

/-- `‖f‖_{L^p([0,1])}` para `f = bumpS`: vale `|a| C₀ t^{1/p}`. -/
lemma eLpNorm_bumpS_le {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {φ : ℝ → ℝ}
    (hφ0 : ∀ z, z ∉ Ioo (0 : ℝ) 1 → φ z = 0) {C0 : ℝ} (hC0 : ∀ z, |φ z| ≤ C0)
    (hC00 : 0 ≤ C0) {a x0 t : ℝ} (ht : 0 < t) :
    eLpNorm (bumpS φ a x0 t) p FormalizacaoLp.vol01 ≤
      ENNReal.ofReal (|a| * C0 * t ^ p.toReal⁻¹) := by
  classical
  have hc : 0 ≤ |a| * C0 := mul_nonneg (abs_nonneg _) hC00
  have hg : ∀ x, |bumpS φ a x0 t x| ≤ (Ioo x0 (x0 + t)).indicator (fun _ => |a| * C0) x := by
    intro x
    by_cases hx : x ∈ Ioo x0 (x0 + t)
    · rw [Set.indicator_of_mem hx]; exact abs_bumpS_le hC0 a x0 t x
    · simp [Set.indicator_of_notMem hx, bumpS_eq_zero hφ0 ht hx]
  have hbound := eLpNorm_le_of_indicator hp0 hpt measurableSet_Ioo hc hg
    FormalizacaoLp.vol01 Measure.restrict_le_self
  refine hbound.trans ?_
  rw [Real.volume_Ioo, show x0 + t - x0 = t by ring, ENNReal.ofReal_rpow_of_nonneg ht.le
    (by positivity), ← ENNReal.ofReal_mul hc]

/-- Mudança para o caso `h` fixo: cota em `L^p` de `Δ²_h` com constante `min{4|a|C₀, |a|M(h/t)²}`. -/
lemma eLpNorm_diff2_bumpS_le {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {φ : ℝ → ℝ}
    (hφ0 : ∀ z, z ∉ Ioo (0 : ℝ) 1 → φ z = 0) {C0 M : ℝ} (hC0 : ∀ z, |φ z| ≤ C0)
    (hC00 : 0 ≤ C0) (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ))
    (hM : ∀ z, |deriv (deriv φ) z| ≤ M) (hM0 : 0 ≤ M)
    {a x0 t : ℝ} (ht : 0 < t) {h : ℝ} (hh : 0 ≤ h) (μ : Measure ℝ) (hμ : μ ≤ volume) :
    eLpNorm (diff2 h (bumpS φ a x0 t)) p μ ≤
      ENNReal.ofReal (min (4 * (|a| * C0)) (|a| * M * (h / t) ^ 2) * (3 * t) ^ p.toReal⁻¹) := by
  have hc : 0 ≤ min (4 * (|a| * C0)) (|a| * M * (h / t) ^ 2) :=
    le_min (by have := mul_nonneg (abs_nonneg a) hC00; linarith)
      (by have := mul_nonneg (abs_nonneg a) hM0; positivity)
  have hr : 0 ≤ p.toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  calc eLpNorm (diff2 h (bumpS φ a x0 t)) p μ
      ≤ ENNReal.ofReal (min (4 * (|a| * C0)) (|a| * M * (h / t) ^ 2)) *
          volume (supU x0 t h) ^ p.toReal⁻¹ :=
        eLpNorm_le_of_indicator hp0 hpt (measurableSet_supU x0 t h) hc
          (abs_diff2_bumpS_le_indicator hφ0 hC0 hφ hφ' hM hM0 ht hh) μ hμ
    _ ≤ ENNReal.ofReal (min (4 * (|a| * C0)) (|a| * M * (h / t) ^ 2)) *
          ENNReal.ofReal ((3 * t) ^ p.toReal⁻¹) := by
        apply mul_le_mul_left'
        rw [← ENNReal.ofReal_rpow_of_nonneg (by linarith) hr]
        exact ENNReal.rpow_le_rpow (volume_supU_le x0 t h ht) hr
    _ = ENNReal.ofReal (min (4 * (|a| * C0)) (|a| * M * (h / t) ^ 2) * (3 * t) ^ p.toReal⁻¹) := by
        rw [ENNReal.ofReal_mul hc]

/-- Cota de módulo de continuidade: `ω_p(bumpS, τ) ≤ K |a| (3t)^{1/p} min{1,(τ/t)²}`, `K = max{4C₀,M}`. -/
theorem wtP_bumpS_le {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {φ : ℝ → ℝ}
    (hφ0 : ∀ z, z ∉ Ioo (0 : ℝ) 1 → φ z = 0) {C0 M : ℝ} (hC0 : ∀ z, |φ z| ≤ C0)
    (hC00 : 0 ≤ C0) (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ))
    (hM : ∀ z, |deriv (deriv φ) z| ≤ M) (hM0 : 0 ≤ M)
    {a x0 t : ℝ} (ht : 0 < t) (τ : ℝ) :
    wtP p τ (bumpS φ a x0 t) ≤
      ENNReal.ofReal (max (4 * C0) M * |a| * (3 * t) ^ p.toReal⁻¹ * min 1 ((τ / t) ^ 2)) := by
  unfold wtP
  refine iSup₂_le fun h hh => ?_
  have hh0 : 0 < h := hh.1
  have hhτ : h ≤ τ := le_trans hh.2 (min_le_left _ _)
  have hR : 0 ≤ (3 * t) ^ p.toReal⁻¹ := by positivity
  set K := max (4 * C0) M with hKdef
  have h4 : 4 * C0 ≤ K := le_max_left _ _
  have hMK : M ≤ K := le_max_right _ _
  have habs : 0 ≤ |a| := abs_nonneg a
  have hy0 : 0 ≤ (h / t) ^ 2 := by positivity
  have key1 : min (4 * (|a| * C0)) (|a| * M * (h / t) ^ 2) ≤ K * |a| * min 1 ((h / t) ^ 2) := by
    rcases le_total ((h / t) ^ 2) 1 with hy | hy
    · rw [min_eq_right hy]
      calc min (4 * (|a| * C0)) (|a| * M * (h / t) ^ 2) ≤ |a| * M * (h / t) ^ 2 := min_le_right _ _
        _ ≤ K * |a| * (h / t) ^ 2 := by nlinarith [mul_nonneg habs hy0]
    · rw [min_eq_left hy]
      calc min (4 * (|a| * C0)) (|a| * M * (h / t) ^ 2) ≤ 4 * (|a| * C0) := min_le_left _ _
        _ ≤ K * |a| * 1 := by nlinarith [mul_nonneg habs hC00]
  have key2 : min 1 ((h / t) ^ 2) ≤ min 1 ((τ / t) ^ 2) := by
    apply min_le_min le_rfl
    exact pow_le_pow_left₀ (div_nonneg hh0.le ht.le) (div_le_div_of_nonneg_right hhτ ht.le) 2
  have hK0 : 0 ≤ K := le_trans (by linarith [hC00]) h4
  have hKa : 0 ≤ K * |a| := mul_nonneg hK0 habs
  refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
  refine (eLpNorm_diff2_bumpS_le hp0 hpt hφ0 hC0 hC00 hφ hφ' hM hM0 ht hh0.le volume le_rfl).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hmin : 0 ≤ min 1 ((τ / t) ^ 2) := le_min zero_le_one (by positivity)
  calc min (4 * (|a| * C0)) (|a| * M * (h / t) ^ 2) * (3 * t) ^ p.toReal⁻¹
      ≤ K * |a| * min 1 ((h / t) ^ 2) * (3 * t) ^ p.toReal⁻¹ :=
        mul_le_mul_of_nonneg_right key1 hR
    _ ≤ K * |a| * min 1 ((τ / t) ^ 2) * (3 * t) ^ p.toReal⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ hR
        exact mul_le_mul_of_nonneg_left key2 hKa
    _ = max (4 * C0) M * |a| * (3 * t) ^ p.toReal⁻¹ * min 1 ((τ / t) ^ 2) := by
        rw [hKdef]; ring

end FormalizacaoAltura
