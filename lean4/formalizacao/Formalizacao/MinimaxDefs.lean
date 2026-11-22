import Formalizacao.ArithmeticFloor
import Formalizacao.UnifSup

/-!
# F2, entrega 1: definições minimax

* `aPS p s`: o expoente `a(p,s)` do Teorema 5.2, por casos como em `lp:thm:minimax-nh`.
* `Dfun p s q N H`: o funcional `D_{p,s,q}(N,H)` = sup, sobre funções mensuráveis com
  `‖f‖*_{B^s_{p,q}} ≤ 1`, do melhor erro `e^H_{N,p}(f)` em `L^p([0,1])`.
* `aPS_eq_nuHat`: no domínio `1 ≤ p`, `0 < s < 2`, `aPS p s = nuHat p s`.
* Lemas estruturais de introdução (`le_Dfun`) e de erro uniforme (`le_bestError_of_forall`).
-/

open scoped ENNReal
open MeasureTheory Set

namespace FormalizacaoMinimax

open FormalizacaoFloor FormalizacaoLow

/-- Expoente `a(p,s)` de `lp:thm:minimax-nh`. -/
noncomputable def aPS (p s : ℝ) : ℝ :=
  if s < 1 / p then 1 + 1 / p - s
  else if s ≤ 1 then 1
  else s

/-- Funcional minimax `D_{p,s,q}(N,H) = sup_{‖f‖* ≤ 1} e^H_{N,p}(f)`. -/
noncomputable def Dfun (p s : ℝ) (q : ENNReal) (N H : ℕ) : ENNReal :=
  ⨆ (f : ℝ → ℝ) (_ : Measurable f) (_ : besovNorm (ENNReal.ofReal p) s q f ≤ 1),
    bestError (ENNReal.ofReal p) N H f

lemma aPS_of_lt {p s : ℝ} (h : s < 1 / p) : aPS p s = 1 + 1 / p - s := by
  unfold aPS
  rw [if_pos h]

lemma aPS_of_mid {p s : ℝ} (h1 : 1 / p ≤ s) (h2 : s ≤ 1) : aPS p s = 1 := by
  unfold aPS
  rw [if_neg (not_lt.mpr h1), if_pos h2]

lemma aPS_of_gt {p s : ℝ} (hp : 1 ≤ p) (h : 1 < s) : aPS p s = s := by
  have hinv : 1 / p ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hp
  unfold aPS
  rw [if_neg (show ¬ s < 1 / p by linarith), if_neg (show ¬ s ≤ 1 by linarith)]

/-- Positividade de `a(p,s)` no domínio do teorema. -/
lemma aPS_pos {p s : ℝ} (hp : 1 ≤ p) (hs0 : 0 < s) : 0 < aPS p s := by
  have hinv : 1 / p ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hp
  unfold aPS
  split_ifs with h1 h2
  · linarith
  · norm_num
  · linarith [not_le.mp h2]

/-- Identidade `aPS = nuHat` no domínio `1 ≤ p`, `0 < s < 2`. -/
lemma aPS_eq_nuHat {p s : ℝ} (hp : 1 ≤ p) : aPS p s = nuHat p s := by
  have hinv : 1 / p ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hp
  unfold aPS nuHat
  split_ifs <;> first
    | rfl
    | (exfalso; linarith)
    | (rw [max_eq_left (show s ≤ 1 by linarith)])
    | (rw [max_eq_right (show (1 : ℝ) ≤ s by linarith)])

/-- Introdução de uma cota pontual no supremo que define `Dfun`. -/
lemma le_Dfun {p s : ℝ} {q : ENNReal} {N H : ℕ} {f : ℝ → ℝ} {d : ENNReal}
    (hf : Measurable f) (hb : besovNorm (ENNReal.ofReal p) s q f ≤ 1)
    (hd : d ≤ bestError (ENNReal.ofReal p) N H f) : d ≤ Dfun p s q N H := by
  unfold Dfun
  exact le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hb hd))

/-- Um limite inferior uniforme sobre `Σ_{N,H}` vale para o ínfimo `bestError`. -/
lemma le_bestError_of_forall {p : ENNReal} {N H : ℕ} {f : ℝ → ℝ} {d : ENNReal}
    (h : ∀ g ∈ Pendencias.Agenda.Sigma (fun _ ↦ H) N, d ≤ FormalizacaoLp.distP p f g) :
    d ≤ bestError p N H f :=
  le_iInf₂ fun g hg => h g hg

end FormalizacaoMinimax
