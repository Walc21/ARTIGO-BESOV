import Mathlib

/-!
# Arcabouço abstrato do módulo (M1 do plano de formalização)

Formaliza o arcabouço da seção «Plano de formalização em Lean 4» do rascunho:
um módulo `ω` sobre um espaço seminormado `X`, com os três axiomas
(subaditividade, cota `ω g t ≤ 4‖g‖`, monotonia em `t`) e positividade.

Sobre esses dados definem-se o funcional de realização `R_N`, o estrato
`R^s_q(G)` e o espaço de Besov `B^s_q` (sequências dos módulos dos dados).
Provam-se a desigualdade inversa (Proposição `lp:prop:inverse`) e a inclusão
`R^s_q(G) ⊆ B^s_q` (Corolário `lp:cor:inclusion`), uma vez, para qualquer
módulo que satisfaça os axiomas. A instanciação em `L^p` é feita à parte.
-/

open scoped ENNReal

namespace Formalizacao

/-- Dados de um módulo abstrato sobre um espaço seminormado `X`. -/
structure ModuloAbs (X : Type*) [SeminormedAddCommGroup X] where
  /-- O módulo `ω(f, t)`. -/
  ω : X → ℝ → ℝ
  /-- Positividade. -/
  nonneg : ∀ (f : X) (t : ℝ), 0 ≤ ω f t
  /-- Subaditividade. -/
  subadd : ∀ (f g : X) (t : ℝ), ω (f + g) t ≤ ω f t + ω g t
  /-- Cota pela norma: `ω g t ≤ 4‖g‖`. -/
  bound : ∀ (g : X) (t : ℝ), ω g t ≤ 4 * ‖g‖
  /-- Monotonia em `t`. -/
  mono : ∀ (f : X) {s t : ℝ}, s ≤ t → ω f s ≤ ω f t

variable {X : Type*} [SeminormedAddCommGroup X]

namespace ModuloAbs

variable (M : ModuloAbs X)

/-- Funcional de realização `R_N(f) = inf_{g ∈ G_N} (‖f - g‖ + ω(g, 1/N))`. -/
noncomputable def realization (G : ℕ → Set X) (N : ℕ) (f : X) : ℝ :=
  sInf ((fun g => ‖f - g‖ + M.ω g (1 / (N : ℝ))) '' G N)

/-- Estrato reversível `R^s_q(G) = {f : (2^{(r+1)s} R_{2^{r+1}}(f))_{r≥0} ∈ ℓ^q}`.
(O índice `r+1` substitui o `r ≥ 1` do rascunho, para começar em `0`.) -/
def stratum (G : ℕ → Set X) (s : ℝ) (q : ℝ≥0∞) : Set X :=
  {f | Memℓp (fun r : ℕ => (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s) * M.realization G (2 ^ (r + 1)) f) q}

/-- Espaço de Besov abstrato: `(2^{rs} ω(f, 2^{-r}))_{r≥0} ∈ ℓ^q`. -/
def besov (s : ℝ) (q : ℝ≥0∞) : Set X :=
  {f | Memℓp (fun r : ℕ => (2 : ℝ) ^ ((r : ℝ) * s) * M.ω f (1 / (2 : ℝ) ^ r)) q}

end ModuloAbs

open ModuloAbs

/-- Desigualdade inversa (Proposição `lp:prop:inverse`, primeira parte):
`ω(f, 1/N) ≤ 4 R_N(f)` para toda família que contém `0`. -/
theorem inverse_le (M : ModuloAbs X) (G : ℕ → Set X) (h0 : ∀ N, (0 : X) ∈ G N)
    (N : ℕ) (f : X) :
    M.ω f (1 / (N : ℝ)) ≤ 4 * M.realization G N f := by
  unfold ModuloAbs.realization
  have hne : ((fun g => ‖f - g‖ + M.ω g (1 / (N : ℝ))) '' G N).Nonempty :=
    ⟨_, ⟨0, h0 N, rfl⟩⟩
  have key : M.ω f (1 / (N : ℝ)) / 4 ≤
      sInf ((fun g => ‖f - g‖ + M.ω g (1 / (N : ℝ))) '' G N) := by
    apply le_csInf hne
    rintro _ ⟨g, -, rfl⟩
    have h1 : M.ω f (1 / (N : ℝ)) ≤ M.ω (f - g) (1 / (N : ℝ)) + M.ω g (1 / (N : ℝ)) := by
      simpa using M.subadd (f - g) g (1 / (N : ℝ))
    have h2 := M.bound (f - g) (1 / (N : ℝ))
    have h3 := M.nonneg g (1 / (N : ℝ))
    have h4 : 0 ≤ ‖f - g‖ := norm_nonneg _
    linarith
  linarith

/-- Se `0 ∈ G_N`, então `R_N(f) ≤ ‖f‖` (Proposição `lp:prop:inverse`, segunda parte). -/
theorem realization_le_norm (M : ModuloAbs X) (G : ℕ → Set X) (N : ℕ) (f : X)
    (h0 : (0 : X) ∈ G N) :
    M.realization G N f ≤ ‖f‖ := by
  unfold ModuloAbs.realization
  have hbdd : BddBelow ((fun g => ‖f - g‖ + M.ω g (1 / (N : ℝ))) '' G N) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨g, -, rfl⟩
    exact add_nonneg (norm_nonneg _) (M.nonneg g _)
  refine le_trans (csInf_le hbdd ⟨0, h0, rfl⟩) ?_
  have hz := M.bound 0 (1 / (N : ℝ))
  simp only [norm_zero, mul_zero] at hz
  simp only [sub_zero]
  linarith

/-- `R_N(f) ≥ 0`, pois é ínfimo de quantidades não negativas. -/
theorem realization_nonneg (M : ModuloAbs X) (G : ℕ → Set X) (N : ℕ) (f : X) :
    0 ≤ M.realization G N f := by
  unfold ModuloAbs.realization
  apply Real.sInf_nonneg
  rintro _ ⟨g, -, rfl⟩
  exact add_nonneg (norm_nonneg _) (M.nonneg g _)

/-- Uma sequência real dominada por `b` (a menos do índice `0`) e com `b ∈ ℓ^q`
está em `ℓ^q`, para `0 < q`. -/
theorem memℓp_of_succ_le {a b : ℕ → ℝ} {q : ℝ≥0∞} (hq : 0 < q)
    (ha : ∀ n, 0 ≤ a (n + 1)) (hb : Memℓp b q) (hab : ∀ n, a (n + 1) ≤ 4 * b n)
    (hb0 : ∀ n, 0 ≤ b n) :
    Memℓp a q := by
  rcases eq_or_ne q ∞ with rfl | hq'
  · -- caso `q = ∞`: limitação
    rw [memℓp_infty_iff] at hb ⊢
    obtain ⟨C, hC⟩ := hb
    refine ⟨max ‖a 0‖ (4 * C), ?_⟩
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero => exact le_max_left _ _
    | succ n =>
      have h1 : ‖a (n + 1)‖ = a (n + 1) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (ha n)]
      have hbn : b n ≤ C := by
        have := hC ⟨n, rfl⟩
        simpa [Real.norm_eq_abs, abs_of_nonneg (hb0 n)] using this
      show ‖a (n + 1)‖ ≤ max ‖a 0‖ (4 * C)
      rw [h1]
      exact le_trans (hab n) (le_trans (by linarith [hbn]) (le_max_right _ _))
  · -- caso `0 < q < ∞`: soma de potências
    have hp : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hq'
    rw [memℓp_gen_iff hp] at hb ⊢
    have hsum : Summable fun n => (4 : ℝ) ^ q.toReal * ‖b n‖ ^ q.toReal :=
      hb.mul_left _
    have hsucc : Summable fun n => ‖a (n + 1)‖ ^ q.toReal := by
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
      have h1 : ‖a (n + 1)‖ = a (n + 1) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (ha n)]
      have h2 : ‖b n‖ = b n := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hb0 n)]
      rw [h1, h2, ← Real.mul_rpow (by norm_num) (hb0 n)]
      exact Real.rpow_le_rpow (ha n) (hab n) hp.le
    exact (summable_nat_add_iff 1).mp hsucc

/-- Inclusão `R^s_q(G) ⊆ B^s_q` (Corolário `lp:cor:inclusion`), para `0 < q`. -/
theorem stratum_subset_besov (M : ModuloAbs X) (G : ℕ → Set X) (h0 : ∀ N, (0 : X) ∈ G N)
    (s : ℝ) (q : ℝ≥0∞) (hq : 0 < q) :
    M.stratum G s q ⊆ M.besov s q := by
  intro f hf
  have hf' : Memℓp (fun r : ℕ => (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s) *
      M.realization G (2 ^ (r + 1)) f) q := hf
  unfold ModuloAbs.besov
  refine memℓp_of_succ_le (a := fun r : ℕ => (2 : ℝ) ^ ((r : ℝ) * s) * M.ω f (1 / (2 : ℝ) ^ r))
    (b := fun r : ℕ => (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s) *
      M.realization G (2 ^ (r + 1)) f) hq ?_ hf' ?_ ?_
  · intro n
    exact mul_nonneg (by positivity) (M.nonneg f _)
  · intro n
    have hI := inverse_le M G h0 (2 ^ (n + 1)) f
    push_cast at hI
    have hw : (0 : ℝ) ≤ (2 : ℝ) ^ ((((n + 1 : ℕ)) : ℝ) * s) := by positivity
    calc (2 : ℝ) ^ ((((n + 1 : ℕ)) : ℝ) * s) * M.ω f (1 / (2 : ℝ) ^ (n + 1))
        ≤ (2 : ℝ) ^ ((((n + 1 : ℕ)) : ℝ) * s) * (4 * M.realization G (2 ^ (n + 1)) f) :=
          mul_le_mul_of_nonneg_left hI hw
      _ = 4 * ((2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * s) * M.realization G (2 ^ (n + 1)) f) := by ring
  · intro n
    exact mul_nonneg (by positivity) (realization_nonneg M G _ f)

end Formalizacao
