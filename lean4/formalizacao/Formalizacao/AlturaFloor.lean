import Formalizacao.AlturaBesov
import Formalizacao.AlturaTerminal

/-!
# Pisos geométrico e de inclinação (auditoria, Partes II e VI)

Parte I deste arquivo: a função-teste fixa `φB` (um `ContDiffBump`, com `φB = 1` em `[1/4,1/2]` e
suporte em `(1/8, 5/8) ⊂ (0,1)`) e a desigualdade de integração por partes que dá um piso `L¹`
para a distância de `a φB` a qualquer função afim em `[0,1]`:

`a κ ≤ M ∫_0^1 |a φB(y) - (α + β y)| dy`, com `κ = ∫_0^1 (φB')² > 0` e `M ≥ sup |φB''|`.
-/

open MeasureTheory Set intervalIntegral
open scoped ENNReal ContDiff

namespace FormalizacaoAltura

open Artigo FormalizacaoLp FormalizacaoLow

/-! ## A função-teste fixa -/

/-- Bump `C^∞` centrado em `3/8`, com `φ = 1` em `[1/4,1/2]` e suporte em `(1/8,5/8)`. -/
noncomputable def bumpB : ContDiffBump (3 / 8 : ℝ) :=
  { rIn := 1 / 8, rOut := 1 / 4, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

/-- A função-teste `φB : ℝ → ℝ`. -/
noncomputable def φB : ℝ → ℝ := bumpB

lemma φB_smooth : ContDiff ℝ ∞ φB := bumpB.contDiff

lemma φB_nonneg (z : ℝ) : 0 ≤ φB z := bumpB.nonneg

lemma φB_le_one (z : ℝ) : φB z ≤ 1 := bumpB.le_one

lemma φB_abs_le (z : ℝ) : |φB z| ≤ 1 := by
  rw [abs_of_nonneg (φB_nonneg z)]; exact φB_le_one z

lemma bumpB_rIn : bumpB.rIn = 1 / 8 := rfl

lemma bumpB_rOut : bumpB.rOut = 1 / 4 := rfl

lemma φB_one_of_mem {z : ℝ} (hz : z ∈ Icc (1 / 4 : ℝ) (1 / 2)) : φB z = 1 := by
  apply bumpB.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le, bumpB_rIn]
  constructor <;> linarith [hz.1, hz.2]

/-- Fora de `(1/8,5/8)` a função se anula: o suporte é a bola aberta de raio `1/4`. -/
lemma φB_eq_zero_of_not_mem {z : ℝ} (hz : z ∉ Ioo (1 / 8 : ℝ) (5 / 8)) : φB z = 0 := by
  unfold φB
  apply Function.notMem_support.mp
  rw [bumpB.support_eq, bumpB_rOut]
  intro hball
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hball
  apply hz
  constructor <;> linarith [hball.1, hball.2]

lemma φB_eventually_zero_left : φB =ᶠ[nhds 0] fun _ => 0 := by
  filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)] with z hz
  exact φB_eq_zero_of_not_mem (fun h => by linarith [h.1, (Set.mem_Iio.mp hz)])

lemma φB_eventually_zero_right : φB =ᶠ[nhds 1] fun _ => 0 := by
  filter_upwards [Ioi_mem_nhds (by norm_num : (5 / 8 : ℝ) < 1)] with z hz
  exact φB_eq_zero_of_not_mem (fun h => by linarith [h.2, (Set.mem_Ioi.mp hz)])

lemma φB_zero_of_not_Ioo {z : ℝ} (hz : z ∉ Ioo (0 : ℝ) 1) : φB z = 0 := by
  apply φB_eq_zero_of_not_mem
  intro h
  apply hz
  constructor <;> linarith [h.1, h.2]

lemma φB_at_zero : φB 0 = 0 := φB_zero_of_not_Ioo (by simp)

lemma φB_at_one : φB 1 = 0 := φB_zero_of_not_Ioo (by simp)

lemma deriv_φB_at_zero : deriv φB 0 = 0 := by
  rw [φB_eventually_zero_left.deriv_eq]; simp

lemma deriv_φB_at_one : deriv φB 1 = 0 := by
  rw [φB_eventually_zero_right.deriv_eq]; simp

lemma φB_diff : Differentiable ℝ φB := φB_smooth.differentiable (by simp)

lemma deriv_φB_contDiff : ContDiff ℝ ∞ (deriv φB) :=
  (contDiff_infty_iff_deriv.mp φB_smooth).2

lemma deriv_φB_diff : Differentiable ℝ (deriv φB) := deriv_φB_contDiff.differentiable (by simp)

lemma deriv_deriv_φB_cont : Continuous (deriv (deriv φB)) :=
  deriv_φB_contDiff.continuous_deriv (by simp)

/-- Cota uniforme de `φB''` (suporte compacto e continuidade). -/
lemma exists_M_φB : ∃ M : ℝ, 0 < M ∧ ∀ z, |deriv (deriv φB) z| ≤ M := by
  have hcs : HasCompactSupport (deriv (deriv φB)) :=
    HasCompactSupport.deriv (HasCompactSupport.deriv bumpB.hasCompactSupport)
  obtain ⟨C, hC⟩ := deriv_deriv_φB_cont.bounded_above_of_compact_support hcs
  refine ⟨max C 1, by positivity, fun z => ?_⟩
  rw [← Real.norm_eq_abs]
  exact (hC z).trans (le_max_left _ _)

/-! ## Integração por partes: piso `L¹` contra afins -/

/-- `κ = ∫_0^1 (φB')² `. -/
noncomputable def kappaB : ℝ := ∫ y in (0 : ℝ)..1, (deriv φB y) ^ 2

lemma integral_deriv_sq_eq : ∫ y in (0 : ℝ)..1, (deriv φB y) ^ 2 = kappaB := rfl

/-- `∫_0^1 φB φB'' = -κ`. -/
lemma integral_phi_second : ∫ y in (0 : ℝ)..1, φB y * deriv (deriv φB) y = -kappaB := by
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := 1)
    (u := φB) (u' := deriv φB) (v := deriv φB) (v' := deriv (deriv φB))
    (fun x _ => (φB_diff x).hasDerivAt) (fun x _ => (deriv_φB_diff x).hasDerivAt)
    (deriv_φB_contDiff.continuous.intervalIntegrable _ _)
    (deriv_deriv_φB_cont.intervalIntegrable _ _)
  rw [hibp, φB_at_one, φB_at_zero, deriv_φB_at_one, deriv_φB_at_zero]
  have : ∫ x in (0 : ℝ)..1, deriv φB x * deriv φB x = kappaB := by
    unfold kappaB; congr 1; funext x; ring
  rw [this]
  ring

/-- `∫_0^1 φB'' = 0`. -/
lemma integral_second_zero : ∫ y in (0 : ℝ)..1, deriv (deriv φB) y = 0 := by
  rw [intervalIntegral.integral_deriv_eq_sub (f := deriv φB) (fun x _ => deriv_φB_diff x)
    (deriv_deriv_φB_cont.intervalIntegrable _ _), deriv_φB_at_one, deriv_φB_at_zero]
  ring

/-- `∫_0^1 y φB''(y) dy = 0`. -/
lemma integral_y_second_zero : ∫ y in (0 : ℝ)..1, y * deriv (deriv φB) y = 0 := by
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := 1)
    (u := fun y => y) (u' := fun _ => (1 : ℝ)) (v := deriv φB) (v' := deriv (deriv φB))
    (fun x _ => hasDerivAt_id x) (fun x _ => (deriv_φB_diff x).hasDerivAt)
    (continuous_const.intervalIntegrable _ _)
    (deriv_deriv_φB_cont.intervalIntegrable _ _)
  rw [hibp, deriv_φB_at_one, deriv_φB_at_zero]
  have h1 : ∫ x in (0 : ℝ)..1, (1 : ℝ) * deriv φB x = 0 := by
    simp only [one_mul]
    rw [intervalIntegral.integral_deriv_eq_sub (f := φB) (fun x _ => φB_diff x)
      (deriv_φB_contDiff.continuous.intervalIntegrable _ _), φB_at_one, φB_at_zero]
    ring
  rw [h1]
  ring

/-- Piso `L¹` para afins: `a κ ≤ M ∫_0^1 |a φB(y) - (α + β y)| dy` (com `M ≥ sup|φB''|`, `a ≥ 0`). -/
lemma L1_affine_lower {M : ℝ} (hM : 0 < M) (hbd : ∀ z, |deriv (deriv φB) z| ≤ M)
    {a : ℝ} (ha : 0 ≤ a) (α β : ℝ) :
    a * kappaB ≤ M * ∫ y in (0 : ℝ)..1, |a * φB y - (α + β * y)| := by
  have hc1 : Continuous (fun y => φB y * deriv (deriv φB) y) :=
    φB_smooth.continuous.mul deriv_deriv_φB_cont
  have hc2 : Continuous (fun y => deriv (deriv φB) y) := deriv_deriv_φB_cont
  have hc3 : Continuous (fun y => y * deriv (deriv φB) y) := continuous_id.mul deriv_deriv_φB_cont
  have hf : Continuous (fun y => a * φB y - (α + β * y)) :=
    ((continuous_const.mul φB_smooth.continuous)).sub (continuous_const.add (continuous_const.mul continuous_id))
  have hid : ∫ y in (0 : ℝ)..1, (a * φB y - (α + β * y)) * deriv (deriv φB) y = -(a * kappaB) := by
    have e : ∀ y, (a * φB y - (α + β * y)) * deriv (deriv φB) y =
        a * (φB y * deriv (deriv φB) y) - α * deriv (deriv φB) y -
          β * (y * deriv (deriv φB) y) := fun y => by ring
    simp_rw [e]
    have hA : Continuous (fun y => a * (φB y * deriv (deriv φB) y)) := continuous_const.mul hc1
    have hB : Continuous (fun y => α * deriv (deriv φB) y) := continuous_const.mul hc2
    have hC : Continuous (fun y => β * (y * deriv (deriv φB) y)) := continuous_const.mul hc3
    rw [intervalIntegral.integral_sub ((hA.sub hB).intervalIntegrable _ _) (hC.intervalIntegrable _ _),
      intervalIntegral.integral_sub (hA.intervalIntegrable _ _) (hB.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_phi_second, integral_second_zero,
      integral_y_second_zero]
    ring
  have habs : |∫ y in (0 : ℝ)..1, (a * φB y - (α + β * y)) * deriv (deriv φB) y| ≤
      ∫ y in (0 : ℝ)..1, |(a * φB y - (α + β * y)) * deriv (deriv φB) y| :=
    intervalIntegral.abs_integral_le_integral_abs zero_le_one
  rw [hid, abs_neg] at habs
  have hle : ∫ y in (0 : ℝ)..1, |(a * φB y - (α + β * y)) * deriv (deriv φB) y| ≤
      ∫ y in (0 : ℝ)..1, M * |a * φB y - (α + β * y)| := by
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact (hf.mul hc2).abs.intervalIntegrable _ _
    · exact (continuous_const.mul hf.abs).intervalIntegrable _ _
    · intro y _
      rw [abs_mul, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hbd y) (abs_nonneg _) |>.trans_eq (by ring)
  rw [intervalIntegral.integral_const_mul] at hle
  exact (le_abs_self _).trans (habs.trans hle)

/-- `κ > 0`: a derivada de `φB` não se anula identicamente, pelo Teorema do Valor Médio. -/
lemma kappaB_pos : 0 < kappaB := by
  obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_slope φB (by norm_num : (0 : ℝ) < 1 / 4)
    φB_smooth.continuous.continuousOn φB_diff.differentiableOn
  have hcval : deriv φB c = 4 := by
    rw [hdc, φB_one_of_mem (show (1 / 4 : ℝ) ∈ Icc (1 / 4 : ℝ) (1 / 2) by norm_num [Icc]),
      φB_at_zero]
    norm_num
  have hev : ∀ᶠ x in nhds c, deriv φB x ≠ 0 :=
    (deriv_φB_contDiff.continuous.continuousAt).eventually_ne (by rw [hcval]; norm_num)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hc0 : 0 < c := hc.1
  have hc1 : c < 1 / 4 := hc.2
  set r : ℝ := min ε (min c (1 - c)) / 2 with hr
  have hrpos : 0 < r := by
    rw [hr]; apply half_pos; apply lt_min hε; apply lt_min hc0; linarith
  have hrε : r < ε := by
    rw [hr]; have := min_le_left ε (min c (1 - c)); linarith
  have hrc : r < c := by
    rw [hr]; have := min_le_right ε (min c (1 - c)); have := min_le_left c (1 - c); linarith
  have hr1 : r < 1 - c := by
    rw [hr]; have := min_le_right ε (min c (1 - c)); have := min_le_right c (1 - c); linarith
  have hpos : ∀ x ∈ Ioo (c - r) (c + r), 0 < (deriv φB x) ^ 2 := by
    intro x hx
    have hd : dist x c < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2]
    have hne := hball hd
    positivity
  have hfi : IntervalIntegrable (fun x => (deriv φB x) ^ 2) volume (c - r) (c + r) :=
    ((deriv_φB_contDiff.continuous.pow 2)).intervalIntegrable _ _
  have hint : 0 < ∫ x in (c - r)..(c + r), (deriv φB x) ^ 2 :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hfi hpos (by linarith)
  have hmono : ∫ x in (c - r)..(c + r), (deriv φB x) ^ 2 ≤ ∫ x in (0 : ℝ)..1, (deriv φB x) ^ 2 := by
    apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
    · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
    · exact (deriv_φB_contDiff.continuous.pow 2).intervalIntegrable _ _
  unfold kappaB
  linarith

/-- Versão afim em `[1-t,1]`: `∫_{1-t}^1 |a φB((x-(1-t))/t) - (α+βx)| dx ≥ t a κ / M`. -/
lemma L1_affine_interval {M : ℝ} (hM : 0 < M) (hbd : ∀ z, |deriv (deriv φB) z| ≤ M)
    {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (α β : ℝ) :
    t * (a * kappaB / M) ≤
      ∫ x in (1 - t)..1, |a * φB ((x - (1 - t)) / t) - (α + β * x)| := by
  have hsub := L1_affine_lower hM hbd ha (α + β * (1 - t)) (β * t)
  have hcomp := intervalIntegral.integral_comp_mul_add
    (f := fun x => |a * φB ((x - (1 - t)) / t) - (α + β * x)|) (a := (0 : ℝ)) (b := 1)
    (c := t) ht.ne' (1 - t)
  simp only [mul_zero, zero_add, mul_one] at hcomp
  rw [show t + (1 - t) = 1 by ring] at hcomp
  have hint : ∫ y in (0 : ℝ)..1, |a * φB ((t * y + (1 - t) - (1 - t)) / t) -
      (α + β * (t * y + (1 - t)))| = ∫ y in (0 : ℝ)..1, |a * φB y - ((α + β * (1 - t)) + (β * t) * y)| := by
    apply intervalIntegral.integral_congr
    intro y _
    simp only
    have e1 : (t * y + (1 - t) - (1 - t)) / t = y := by field_simp; ring
    rw [e1]
    congr 2
    ring
  rw [hint] at hcomp
  have hI : a * kappaB / M ≤ ∫ y in (0 : ℝ)..1,
      |a * φB y - ((α + β * (1 - t)) + (β * t) * y)| := by
    rw [div_le_iff₀ hM]; linarith [hsub]
  have h2 : ∫ x in (1 - t)..1, |a * φB ((x - (1 - t)) / t) - (α + β * x)| =
      t * ∫ y in (0 : ℝ)..1, |a * φB y - ((α + β * (1 - t)) + (β * t) * y)| := by
    rw [hcomp, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  rw [h2]
  exact mul_le_mul_of_nonneg_left hI ht.le

/-! ## Passagem para `L^p` num intervalo -/

lemma eLpNorm_one_interval {h : ℝ → ℝ} (hh : Continuous h) {c d : ℝ} (hcd : c ≤ d) :
    eLpNorm h 1 (volume.restrict (Icc c d)) = ENNReal.ofReal (∫ x in c..d, |h x|) := by
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm
    hh.integrableOn_Icc, intervalIntegral.integral_of_le hcd, integral_Icc_eq_integral_Ioc]
  simp [Real.norm_eq_abs]

/-- Cota inferior em `L^p(I)` por `L^1(I)` quando `|I| = t`:
`(∫_I |h|) t^{1/p - 1} ≤ ‖h‖_{L^p(I)}`. -/
lemma lp_lower_of_L1 {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) {h : ℝ → ℝ} (hh : Continuous h)
    {c t : ℝ} (ht : 0 < t) (hct : c + t = 1) :
    ENNReal.ofReal ((∫ x in c..(c + t), |h x|) * t ^ (p.toReal⁻¹ - 1)) ≤
      eLpNorm h p (volume.restrict (Icc c (c + t))) := by
  set μ := volume.restrict (Icc c (c + t)) with hμ
  have hmu : μ Set.univ = ENNReal.ofReal t := by
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Icc]; congr 1; ring
  have hkey := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (f := h) (p := 1) (q := p)
    hp1 hh.aestronglyMeasurable
  have hp1r : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp1
    simpa using this
  have hinv : p.toReal⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1r
  have hexp : (1 : ℝ) / (1 : ℝ≥0∞).toReal - 1 / p.toReal = 1 - p.toReal⁻¹ := by
    simp [one_div]
  rw [hmu, hexp, ENNReal.ofReal_rpow_of_nonneg ht.le (by linarith),
    eLpNorm_one_interval hh (by linarith)] at hkey
  have hI : 0 ≤ ∫ x in c..(c + t), |h x| :=
    intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  have hX : ENNReal.ofReal (t ^ (1 - p.toReal⁻¹)) * ENNReal.ofReal (t ^ (p.toReal⁻¹ - 1)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht]
    norm_num
  calc ENNReal.ofReal ((∫ x in c..(c + t), |h x|) * t ^ (p.toReal⁻¹ - 1))
      = ENNReal.ofReal (∫ x in c..(c + t), |h x|) * ENNReal.ofReal (t ^ (p.toReal⁻¹ - 1)) :=
        ENNReal.ofReal_mul hI
    _ ≤ (eLpNorm h p μ * ENNReal.ofReal (t ^ (1 - p.toReal⁻¹))) *
          ENNReal.ofReal (t ^ (p.toReal⁻¹ - 1)) := mul_le_mul_of_nonneg_right hkey (zero_le _)
    _ = eLpNorm h p μ * (ENNReal.ofReal (t ^ (1 - p.toReal⁻¹)) *
          ENNReal.ofReal (t ^ (p.toReal⁻¹ - 1))) := by rw [mul_assoc]
    _ = eLpNorm h p μ := by rw [hX, mul_one]

/-! ## Piso geométrico -/

/-- Todo `g ∈ Σ_N^H` é afim em `[1-1/H, 1]` (zero, ou última folha de uma representação). -/
lemma affine_on_terminal {H N : ℕ} (hH : 1 ≤ H) {g : ℝ → ℝ}
    (hg : g ∈ Pendencias.Agenda.Sigma (fun _ => H) N) :
    ∃ α β : ℝ, EqOn g (fun x => α + β * x) (Icc (1 - 1 / (H : ℝ)) 1) := by
  simp only [Pendencias.Agenda.Sigma, Set.mem_setOf_eq] at hg
  rcases hg with rfl | ⟨T, hadm, rfl⟩
  · exact ⟨0, 0, fun x _ => by simp⟩
  · obtain ⟨hWF, _, hmax⟩ := hadm
    obtain ⟨a, _, hA⟩ := terminal_affine hWF hmax hH
    refine ⟨a.y0 - a.s * a.x0, a.s, fun x hx => ?_⟩
    simp only
    rw [hA x hx, Artigo.Atom.eval]
    ring

/-- Piso geométrico para uma distância individual: `distP(f,g) ≥ a κ t^{1/p} / M`. -/
lemma geometric_dist_lower {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) {M : ℝ} (hM : 0 < M)
    (hbd : ∀ z, |deriv (deriv φB) z| ≤ M) {H N : ℕ} (hH : 2 ≤ H) {a : ℝ} (ha : 0 ≤ a)
    {g : ℝ → ℝ} (hg : g ∈ Pendencias.Agenda.Sigma (fun _ => H) N) :
    ENNReal.ofReal (a * kappaB / M * (1 / (H : ℝ)) ^ p.toReal⁻¹) ≤
      distP p (bumpS φB a (1 - 1 / (H : ℝ)) (1 / (H : ℝ))) g := by
  set t : ℝ := 1 / (H : ℝ) with ht_def
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have ht : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht_def, div_le_one hHpos]; exact_mod_cast (show 1 ≤ H by omega)
  obtain ⟨α, β, hab⟩ := affine_on_terminal (by omega) hg
  set f := bumpS φB a (1 - t) t with hf
  have hfc : Continuous f := by
    rw [hf]; unfold bumpS
    exact continuous_const.mul (φB_smooth.continuous.comp
      ((continuous_id.sub continuous_const).div_const t))
  set h : ℝ → ℝ := fun x => a * φB ((x - (1 - t)) / t) - (α + β * x) with hh_def
  have hhc : Continuous h := by
    rw [hh_def]
    exact (continuous_const.mul (φB_smooth.continuous.comp
      ((continuous_id.sub continuous_const).div_const t))).sub
      (continuous_const.add (continuous_const.mul continuous_id))
  have hcT : (1 - t) + t = 1 := by ring
  have hLp := lp_lower_of_L1 hp1 hpt hhc ht (c := 1 - t) (by linarith)
  rw [hcT] at hLp
  have hL1 := L1_affine_interval hM hbd ha ht ht1 α β
  -- substituição `g = ℓ` em `[1-t, 1]`
  have hμ : (f - g) =ᵐ[volume.restrict (Icc (1 - t) 1)] h := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp only [Pi.sub_apply, hf, bumpS, hh_def]
    rw [hab hx]
  have hmono : eLpNorm (f - g) p (volume.restrict (Icc (1 - t) 1)) ≤
      distP p (bumpS φB a (1 - t) t) g := by
    unfold distP
    apply eLpNorm_mono_measure
    exact Measure.restrict_mono
      (show Icc (1 - t) 1 ⊆ Icc (0 : ℝ) 1 from fun x hx => ⟨by linarith [hx.1], hx.2⟩) le_rfl
  have heq : eLpNorm h p (volume.restrict (Icc (1 - t) 1)) =
      eLpNorm (f - g) p (volume.restrict (Icc (1 - t) 1)) := (eLpNorm_congr_ae hμ).symm
  have hexp : t ^ p.toReal⁻¹ = t * t ^ (p.toReal⁻¹ - 1) := by
    have := Real.rpow_add ht 1 (p.toReal⁻¹ - 1)
    rw [Real.rpow_one, show (1 : ℝ) + (p.toReal⁻¹ - 1) = p.toReal⁻¹ by ring] at this
    exact this
  calc ENNReal.ofReal (a * kappaB / M * t ^ p.toReal⁻¹)
      = ENNReal.ofReal ((t * (a * kappaB / M)) * t ^ (p.toReal⁻¹ - 1)) := by
        congr 1; rw [hexp]; ring
    _ ≤ ENNReal.ofReal ((∫ x in (1 - t)..1, |h x|) * t ^ (p.toReal⁻¹ - 1)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hL1 (Real.rpow_nonneg ht.le _))
    _ ≤ eLpNorm h p (volume.restrict (Icc (1 - t) 1)) := hLp
    _ = eLpNorm (f - g) p (volume.restrict (Icc (1 - t) 1)) := heq
    _ ≤ distP p (bumpS φB a (1 - t) t) g := hmono

/-- **Piso geométrico em toda a biblioteca.** Para `H ≥ 2` existe `f_H` na bola de Besov unitária
com `dist_{L^p}(f_H, g) ≥ c H^{-s}` para todo `g ∈ Σ_N^H` e todo `N`. -/
theorem geometric_floor {p q : ℝ≥0∞} {s : ℝ} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) (hq0 : 0 < q)
    (hs : 0 < s) (hs2 : s < 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ H : ℕ, 2 ≤ H → ∃ f : ℝ → ℝ, Measurable f ∧ besovNorm p s q f ≤ 1 ∧
      ∀ N : ℕ, ∀ g ∈ Pendencias.Agenda.Sigma (fun _ => H) N,
        ENNReal.ofReal (c * (H : ℝ) ^ (-s)) ≤ distP p f g := by
  obtain ⟨M, hM, hbd⟩ := exists_M_φB
  obtain ⟨Λ, hΛ0, hΛ⟩ := besovNorm_bumpS_le hp1 hpt hq0 hs hs2 (φ := φB)
    (fun z hz => φB_zero_of_not_Ioo hz) (C0 := 1) φB_abs_le zero_le_one φB_diff deriv_φB_diff
    hbd hM.le
  set Λ' : ℝ := max Λ 1 with hΛ'
  have hΛ'pos : 0 < Λ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hΛΛ' : Λ ≤ Λ' := le_max_left _ _
  refine ⟨kappaB / (M * Λ'), by have := kappaB_pos; positivity, fun H hH => ?_⟩
  set t : ℝ := 1 / (H : ℝ) with ht_def
  set e : ℝ := p.toReal⁻¹ with he
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have ht : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht_def, div_le_one hHpos]; exact_mod_cast (show 1 ≤ H by omega)
  set a : ℝ := t ^ (s - e) / Λ' with ha_def
  have ha : 0 ≤ a := by positivity
  refine ⟨bumpS φB a (1 - t) t, ?_, ?_, ?_⟩
  · -- mensurabilidade
    have hc : Continuous (bumpS φB a (1 - t) t) := by
      unfold bumpS
      exact continuous_const.mul (φB_smooth.continuous.comp
        ((continuous_id.sub continuous_const).div_const t))
    exact hc.measurable
  · -- norma de Besov unitária
    refine (hΛ a (1 - t) t ht ht1).trans ?_
    apply ENNReal.ofReal_le_one.mpr
    have hprod : Λ * |a| * t ^ (e - s) = Λ / Λ' := by
      have h1 : t ^ (s - e) * t ^ (e - s) = 1 := by
        rw [← Real.rpow_add ht]
        norm_num
      rw [abs_of_nonneg ha, ha_def]
      calc Λ * (t ^ (s - e) / Λ') * t ^ (e - s) = Λ / Λ' * (t ^ (s - e) * t ^ (e - s)) := by ring
        _ = Λ / Λ' := by rw [h1, mul_one]
    rw [hprod]
    rw [div_le_one hΛ'pos]
    exact hΛΛ'
  · intro N g hg
    have hdist := geometric_dist_lower hp1 hpt hM hbd hH ha hg
    rw [← ht_def, ← he] at hdist
    refine le_trans (le_of_eq ?_) hdist
    congr 1
    have hx : t ^ (s - e) * t ^ e = t ^ s := by
      rw [← Real.rpow_add ht]; congr 1; ring
    have hts : t ^ s = (H : ℝ) ^ (-s) := by
      rw [ht_def, one_div, Real.inv_rpow hHpos.le, Real.rpow_neg hHpos.le]
    rw [ha_def, ← hts, ← hx]
    ring

end FormalizacaoAltura
