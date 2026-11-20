import Formalizacao.LpJackson1
import Formalizacao.Lemma55
import Formalizacao.Library

/-!
# M8: a hipótese `J_p` é um teorema

`hypJp_of_lt : 1 ≤ p → 1/p < s → HypJp p s`.

Esboço (plano do artigo, `lp:prop:jackson-proof`): `f ∈ B^s_{p,∞}` com `s > 1/p` tem
representante contínuo `G` (M6); os valores nodais `y_j = λ_j(f) = λ_j(G)` são limitados por
`2B` e têm saltos `≤ 1` para `n` grande (M4); a árvore nodal quantizada `T` (M7) tem altura
`≤ H` e fica a `8(2B+1)/H` de `Q_n f` em `[0,1]` (`nodal_tree`); e `‖f - Q_n f‖_p ≤ 9 C_W ω_p`
(M5). A triangular dá `‖f - g‖_p ≤ 9 C_W ω_p + 8(2B+1)/H`.
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoGrid FormalizacaoLp Artigo

namespace FormalizacaoJ

/-- **Núcleo da montagem de `J_p`.** Dadas cotas nodais para `n = 2^r` (`|λ_j(f)| ≤ 2B` e saltos
`≤ 1`) e `H` com `8n ≤ H` e `16(2B+1) ≤ H`, existe `g ∈ A_{n,H}` com
`‖f - g‖_p ≤ 9 C_W ω_p(f,1/n) + 8(2B+1)/H`. -/
theorem lp_jackson_core {p : ℝ} (hp : 1 ≤ p) {CW : ℝ}
    (hq : ∀ n : ℕ, 2 ≤ n → ∀ f : ℝ → ℝ, Measurable f → IntegrableOn f (Icc 0 1) →
      Np p f (Icc 0 1) < ⊤ → Np p (fun x => f x - Q n f x) (Icc 0 1) ≤
        9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {B : ℝ} (hB : 0 ≤ B) {r : ℕ} (hr2 : 2 ≤ 2 ^ r)
    (hlam : ∀ j : ℕ, j ≤ 2 ^ r → |lam (2 ^ r) f j| ≤ 2 * B)
    (hjump : ∀ j : ℕ, j < 2 ^ r → |lam (2 ^ r) f (j + 1) - lam (2 ^ r) f j| ≤ 1)
    {H : ℕ} (hHn : 8 * (2 : ℝ) ^ r ≤ H) (hH16 : 16 * (2 * B + 1) ≤ (H : ℝ)) :
    ∃ g ∈ classNH (2 ^ r) H, eLpNorm (f - g) (ENNReal.ofReal p) vol01 ≤
      9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f +
        ENNReal.ofReal (8 * (2 * B + 1) / H) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  set n : ℕ := 2 ^ r with hn
  have hnR2 : ((2 : ℝ) ^ r) = (n : ℝ) := by rw [hn]; push_cast; ring
  have hn1' : 1 ≤ n := by omega
  have hHn' : 8 * (n : ℝ) ≤ H := by rw [← hnR2]; exact hHn
  have hHpos : (0 : ℝ) < H := by
    have : (0 : ℝ) < n := by exact_mod_cast hn1'
    linarith
  set y : ℤ → ℝ := fun m => lam n f m.toNat with hy
  have hyb : ∀ m : ℤ, 0 ≤ m → m ≤ 2 ^ r → |y m| ≤ 2 * B := by
    intro m h0 h1
    simp only [hy]
    refine hlam m.toNat ?_
    have : m ≤ (n : ℤ) := by rw [hn]; push_cast; exact h1
    omega
  have hk : 0 + r + 1 ≤ H := by
    have h1 : r + 1 ≤ n := by have := Nat.lt_two_pow_self (n := r); rw [hn]; omega
    have h2 : ((r + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
    have h3 : ((r + 1 : ℕ) : ℝ) ≤ H := by
      have : (n : ℝ) ≤ H := by linarith [(by exact_mod_cast hn1' : (1 : ℝ) ≤ n)]
      linarith
    have : r + 1 ≤ H := by exact_mod_cast h3
    omega
  have hm : ∀ m : ℤ, 0 ≤ m → m < 2 ^ r → m.natAbs + 1 ≤ H := by
    intro m h0 h1
    have h1' : m.natAbs < n := by
      have : m < (n : ℤ) := by rw [hn]; push_cast; exact h1
      omega
    have : (m.natAbs + 1 : ℕ) ≤ n := h1'
    have h2 : ((m.natAbs + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    have h3 : ((m.natAbs + 1 : ℕ) : ℝ) ≤ H := by
      have : (n : ℝ) ≤ H := by linarith [(by exact_mod_cast hn1' : (1 : ℝ) ≤ n)]
      linarith
    exact_mod_cast h3
  have hsl : ∀ m : ℤ, 0 ≤ m → m < 2 ^ r →
      (2 : ℝ) ^ (0 + r) * (|y (m + 1) - y m| + 16 * (2 * B + 1) / H) ≤ H := by
    intro m h0 h1
    have hm1 : (m + 1).toNat = m.toNat + 1 := by omega
    have hjn : m.toNat < n := by
      have : m < (n : ℤ) := by rw [hn]; push_cast; exact h1
      omega
    have hd : |y (m + 1) - y m| ≤ 1 := by
      simp only [hy]
      rw [hm1]
      exact hjump m.toNat hjn
    have h3 : (2 : ℝ) ^ (0 + r) = n := by rw [hn]; push_cast; ring
    rw [h3]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1'
    have hb : 0 ≤ 16 * (2 * B + 1) := by positivity
    have e1 : (n : ℝ) * (16 * (2 * B + 1) / H) ≤ 16 * (2 * B + 1) / 8 := by
      rw [← mul_div_assoc, div_le_div_iff₀ hHpos (by norm_num)]
      nlinarith
    calc (n : ℝ) * (|y (m + 1) - y m| + 16 * (2 * B + 1) / H)
        ≤ n * (1 + 16 * (2 * B + 1) / H) := by gcongr
      _ = n + n * (16 * (2 * B + 1) / H) := by ring
      _ ≤ H / 8 + 16 * (2 * B + 1) / 8 := by linarith
      _ ≤ H := by linarith
  obtain ⟨T, hT, hbound⟩ := nodal_tree (r := r) (R := 2 * B) (by positivity) (y := y) hyb hH16 hk hm hsl
  refine ⟨T.eval 0 0, ⟨T, (Pendencias.Jackson.admK_zero _ _ _).1 hT, rfl⟩, ?_⟩
  set g : ℝ → ℝ := T.eval 0 0 with hg
  have hgm : Measurable g := measurable_eval T 0 0
  have hQc : Continuous (Q n f) := FormalizacaoL55.Q_continuous n f
  have hnode : ∀ m : ℤ, 0 ≤ m → m ≤ 2 ^ r → Q n f (cL r m) = y m := by
    intro m h0 h1
    have hk : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h0
    have hcL : cL r m = tn n m.toNat := by
      unfold cL tn; rw [hk, hnR2]
    rw [hcL]
    have : m.toNat ≤ n := by
      have : m ≤ (n : ℤ) := by rw [hn]; push_cast; exact h1
      omega
    exact Q_node hn1' f this
  have hcell : ∀ m : ℤ, 0 ≤ m → m < 2 ^ r → ∃ α β : ℝ, ∀ x ∈ cellIcc r m, Q n f x = α + β * x := by
    intro m h0 h1
    have hk : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h0
    have hlt : m.toNat < n := by
      have : m < (n : ℤ) := by rw [hn]; push_cast; exact h1
      omega
    obtain ⟨α, β, h⟩ := FormalizacaoL55.Q_affine_on_cell hn1' hlt f
    refine ⟨α, β, fun x hx => h x ?_⟩
    have hx' : x ∈ Icc ((m : ℝ) / 2 ^ r) (((m : ℝ) + 1) / 2 ^ r) := hx
    unfold cell tn
    push_cast
    rw [hk]
    rw [hnR2] at hx'
    exact hx'
  have hbd := hbound (Q n f) hnode hcell
  have hbd2 : eLpNorm (fun x => Q n f x - g x) (ENNReal.ofReal p) vol01 ≤
      ENNReal.ofReal (8 * (2 * B + 1) / H) := by
    have hae : ∀ᵐ x ∂vol01, ‖Q n f x - g x‖ ≤ 8 * (2 * B + 1) / H := by
      refine ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => ?_)
      have hx' : x ∈ cellIcc 0 0 := by simpa [cellIcc] using hx
      rw [Real.norm_eq_abs]; exact hbd x hx'
    calc eLpNorm (fun x => Q n f x - g x) (ENNReal.ofReal p) vol01
        ≤ vol01 Set.univ ^ (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal (8 * (2 * B + 1) / H) :=
          eLpNorm_le_of_ae_bound hae
      _ = ENNReal.ofReal (8 * (2 * B + 1) / H) := by
          have : vol01 Set.univ = 1 := by
            simp [vol01, Measure.restrict_apply_univ, Real.volume_Icc]
          rw [this, ENNReal.one_rpow, one_mul]
  have hbd1 : eLpNorm (fun x => f x - Q n f x) (ENNReal.ofReal p) vol01 ≤
      9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f := by
    have := hq n hr2 f hf hfi hfin
    rw [hnR2]
    exact this
  have hsum : eLpNorm (f - g) (ENNReal.ofReal p) vol01 ≤
      eLpNorm (fun x => f x - Q n f x) (ENNReal.ofReal p) vol01 +
        eLpNorm (fun x => Q n f x - g x) (ENNReal.ofReal p) vol01 := by
    have e : f - g = (fun x => f x - Q n f x) + (fun x => Q n f x - g x) := by
      funext x; simp
    rw [e]
    exact eLpNorm_add_le (hf.sub hQc.measurable).aestronglyMeasurable
      (hQc.measurable.sub hgm).aestronglyMeasurable hp1
  exact hsum.trans (add_le_add hbd1 hbd2)

theorem hypJp_of_lt {p s : ℝ} (hp : 1 ≤ p) (hs : 1 / p < s) :
    HypJp (ENNReal.ofReal p) s := by
  intro f hf hbes
  have hp0 : 0 < p := by linarith
  obtain ⟨hfin', hlq⟩ := hbes
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hfin : Np p f (Icc 0 1) < ⊤ := hfin'
  have hfi : IntegrableOn f (Icc 0 1) := by
    have hmem : MemLp f (ENNReal.ofReal p) (volume.restrict (Icc (0 : ℝ) 1)) :=
      ⟨hf.aestronglyMeasurable, hfin'⟩
    exact hmem.integrable hp1
  set S := lqNorm ⊤ (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) *
    wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f) with hSdef
  have hS : S < ⊤ := hlq
  have hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S := by
    intro m
    rw [hSdef, lqNorm, if_pos rfl]
    exact le_iSup (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f) m
  have hGc := FormalizacaoW.Glim_continuousOn_unc hp hf hfi hfin hS hbS hs
  have hae := FormalizacaoW.ae_eq_Glim_unc hp hf hfi hfin hS hbS hs
  obtain ⟨B, hB0, hlam, hsmall⟩ := nodal_G hGc
  obtain ⟨n1, hn1⟩ := hsmall 1 one_pos
  obtain ⟨CW, hCW, hq⟩ := FormalizacaoW.quasi_error_unc hp
  refine ⟨9 * CW, 8 * (2 * B + 1), by positivity, by positivity,
    max n1 (max 2 ⌈2 * (2 * B + 1)⌉₊), ?_⟩
  intro r hr H hH
  set n : ℕ := 2 ^ r with hn
  have hr' : max n1 (max 2 ⌈2 * (2 * B + 1)⌉₊) ≤ n := hr
  have hn1le : n1 ≤ n := (max_le_iff.1 hr').1
  have hn2 : 2 ≤ n := (max_le_iff.1 (max_le_iff.1 hr').2).1
  have hn3 : ⌈2 * (2 * B + 1)⌉₊ ≤ n := (max_le_iff.1 (max_le_iff.1 hr').2).2
  have hnR : 2 * (2 * B + 1) ≤ (n : ℝ) := by
    have := Nat.le_ceil (2 * (2 * B + 1))
    have h2 : (⌈2 * (2 * B + 1)⌉₊ : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  have hn1' : 1 ≤ n := by omega
  have hHn : 8 * (2 : ℝ) ^ r ≤ H := by
    have h1 : 8 * ((2 : ℝ) ^ r) ^ (max 1 s) ≤ H := (le_max_left _ _).trans hH
    have h2 : (2 : ℝ) ^ r ≤ ((2 : ℝ) ^ r) ^ (max 1 s) :=
      Real.self_le_rpow_of_one_le (one_le_pow₀ (by norm_num)) (le_max_left 1 s)
    linarith
  have hHn8 : 8 * (n : ℝ) ≤ H := by
    have h3 : (n : ℝ) = 2 ^ r := by rw [hn]; push_cast; ring
    rw [h3]; exact hHn
  have hH16 : 16 * (2 * B + 1) ≤ (H : ℝ) := by linarith
  have hy_eq : ∀ j : ℕ, lam n f j = lam n (FormalizacaoL55c.Glim f) j := fun j =>
    lam_congr_ae hn1' hae j
  obtain ⟨g, hg, hbound⟩ := lp_jackson_core hp hq hf hfi hfin hB0 hn2
    (fun j hj => by rw [hy_eq]; exact hlam n hn1' j hj)
    (fun j hj => by rw [hy_eq, hy_eq]; exact hn1 n hn1le hn2 j hj) hHn hH16
  refine ⟨g, hg, ?_⟩
  have hR : 0 ≤ (⨆ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |f x|).toReal := ENNReal.toReal_nonneg
  have hCa : ENNReal.ofReal (9 * CW) = 9 * ENNReal.ofReal CW := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  have hHpos : (0 : ℝ) < H := by linarith [(by exact_mod_cast hn1' : (1 : ℝ) ≤ n)]
  have hH' : ENNReal.ofReal (8 * (2 * B + 1) / H) ≤
      ENNReal.ofReal (8 * (2 * B + 1)) *
        ENNReal.ofReal ((⨆ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |f x|).toReal + 1) / (H : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos hHpos, ENNReal.ofReal_natCast]
    refine ENNReal.div_le_div_right ?_ _
    exact le_mul_of_one_le_right (zero_le _) (ENNReal.one_le_ofReal.2 (by linarith))
  calc eLpNorm (f - g) (ENNReal.ofReal p) vol01
      ≤ 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f +
          ENNReal.ofReal (8 * (2 * B + 1) / H) := hbound
    _ ≤ ENNReal.ofReal (9 * CW) * wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f +
          ENNReal.ofReal (8 * (2 * B + 1)) *
            ENNReal.ofReal ((⨆ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |f x|).toReal + 1) /
              (H : ℝ≥0∞) := by
        rw [hCa]
        exact add_le_add le_rfl hH'

end FormalizacaoJ
