# Auditoria de fidelidade: enunciados Lean × texto de `conjecturas_lp.tex`

Escopo: definições (§2) e enunciados dos resultados principais (§§3–5) comparados com as
declarações Lean. Veredito por item: **fiel** (mesmo conteúdo), **diferença documentada**
(equivalente sob as escolhas de formalização, já explicitadas no artigo), **mais geral** (Lean
prova mais do que o texto afirma) ou **a corrigir**.

## Definições

| Item | Texto | Lean | Veredito |
|---|---|---|---|
| Diferença `Δ²_h` e módulo `ω_p` | `lp:eq:second-difference`, `lp:eq:modulus-p`: sup sobre `0<h≤min{t,1/2}`, norma em `[0,1-2h]` | `diff2`, `wtP` | fiel |
| Besov `B^s_{p,q}` | `lp:eq:besov-p`: `f∈L^p` e `(2^{rs}ω_p(f,2^{-r}))_{r≥0} ∈ ℓ^q` | `besovP` (`eLpNorm < ⊤` e `lqNorm`) | fiel |
| Realização `R_N^G(f)_p` | `lp:eq:realization-p` | `realP` (`distP` com `vol01`) | fiel |
| Estrato `R^s_q` | `lp:eq:stratum-p`, índice `r≥1` | `stratumP`, índice `r+1` | fiel (reindexação documentada) |
| `Σ_N` | `{0} ∪ A_{N,H(N)}` | `Sigma H N` | fiel |
| Agenda `H_{s,κ}` | `⌈8(N+1)^{ν_s}[log(eN)]^κ⌉`, `ν_s=max{1,s}` | `Hsk` | fiel |
| Agenda `H̃_{s,η}` | `⌈8(N+1)^{max{1,s+η}}⌉` | `HtilK` (com `CK 0 0 = 8`) | fiel |
| Família aninhada, contém `Σ` | `lp:def:network-family` | `Conj2Stability` | fiel, com a exigência de mensurabilidade (ver abaixo) |

## Resultados

| Resultado | Texto | Lean | Veredito |
|---|---|---|---|
| Lema 4.1 (módulo) | subaditividade, `ω≤4‖g‖`, monotonia | `wtP_add_le`, `wtP_le_four`, `wtP_mono_t` | fiel |
| Prop 4.2 (inversa) | `ω_p(f,1/N)≤4R_N^G(f)`; `R≤‖f‖` se `0∈G_N` | `wtP_le_four_realP`, `realP_le_norm` | fiel; Lean vale para todo `N` (mais geral) |
| Cor 4.3 (inclusão) | `R^s_q(G)⊂B^s_{p,q}`, `0<q≤∞`, sem `s<2` | `stratum_subset_besov_conn` | fiel |
| Lema 5.1 (núcleo de `P_I`) | `|(P_Ih)(e)|≤4ℓ^{-1/p}‖h‖_{L^p(I)}`; `≤2‖h‖_∞`; `P_I` é a projeção ortogonal em afins | `abs_integral_kernel_le`, `abs_integral_kL_mul_le`, `kernel_is_affine_projection`, `kL_eq_Kf`, `kR_eq_Kf` | fiel (identidade do núcleo agora formalizada, correção 4) |
| Lema 5.2(a),(b) | `Q_n` linear, reproduz afins; `‖f−Q_nf‖_{L^p(I_k)}≤9E(f,J_k)_p` | `Q_affine`, `local_error_inf` | fiel |
| Lema 5.2(c) | `|λ_j|≤2‖f‖_∞` | `abs_lam_sup_le` (cota por `M` sobre a célula) | fiel (forma mais geral) |
| Lema 5.2(d) | `|λ_{j+1}−λ_j|≤5ω_1(f,1/n)_∞` | `lam_diff_le` com `omega1` (sup sobre `|x−y|≤1/n` em `[0,1]`) | fiel (sup com `h≤t` é o mesmo que `|x−y|≤t`) |
| Lema 5.3 (Whitney) | `(Σ_k E(f,J_k)^p)^{1/p} ≤ C_W ω_p(f,1/n)`, `C_W≥1` | `whitney_lp` (`WhitneyLp`, `C_W≥0`); `J_k = Jcell` | fiel; diferença trivial: `C_W≥0` no Lean |
| Cor 5.4 | `‖f−Q_nf‖_p ≤ 9C_W ω_p(f,1/n)` | `quasi_error_unc` | fiel |
| Lema 5.5(a) | `G` contínua, `|G|≤C‖f‖*`, `G=f` q.t.p. | `Glim_continuousOn_unc`, `Glim_bound`, `ae_eq_Glim_unc` | fiel |
| Lema 5.5(b), `s'<1` | `ω_1(f,t)≤C‖f‖*t^{s'}` | `modulus_lt1_unc` | fiel; constante Lean depende de `S` (≈`‖f‖*`) |
| Lema 5.5(b), `s'=1` | `ω_1≤C‖f‖* t log(e/t)` | `modulus_eq1_unc`: `C·t(1+log(1/t))` | fiel (`t log(e/t) = t(1+log(1/t))`) |
| Lema 5.5(b), `s'>1` | `ω_1≤C‖f‖* t`, `1<s'<2−1/p` | `modulus_gt1_unc` (sem o limite superior) | mais geral; não afeta `s<2` |
| Prop 5.6 / `J_p` (forma fraca) | `C_0=C_0(p)`, `C_1` absoluto, `f` contínua | `HypJpStrong`, `hypJpStrong_of_lt`: `C_0=9C_W(p)`, `C_1=16` | fiel |
| `J_p` (forma usada nas reduções) | — | `HypJp`, `hypJp_of_lt`: `C_0, C_1, n_0` dependem de `f`; `R` é o `toReal` do sup pontual | **diferença documentada** (mais fraca) |
| Conj. 1, `q=∞` | `B^s_{p,∞} = R^s_∞(Σ, H_{s,0})` | `conj1_endpoint` | fiel |
| Conj. 1, `s<1` | `0<q<∞`, `1/p<s<1`, `H_{s,0}` | `conj1_subcritical` | fiel |
| Conj. 1, `s≥1` | `1≤s<2`, `κ>1/q`, `H_{s,κ}` | `conj1_critical` (sem `s<2`) | **mais geral** (`s<2` não é usado) |
| Conj. 1, `H̃` | enunciado no regime `1/p<s<2`, `0<q<∞`, `η>0` | `conj1_tilde` (com `hs2 : s < 2`, como no artigo) | fiel |
| Conj. 2 | família aninhada, contém `Σ^H_{⌈cN⌉}`, `c≥1` | `conj2_endpoint`, `_subcritical`, `_critical`, `_tilde` (este último com `hs2 : s < 2`) | fiel |
| Estabilidade aproximada | inclusão aproximada em `L^p` com `(2^{rs}ε_{2^r}) ∈ ℓ^q` | `conj2_approx_endpoint`, `_subcritical`, `_critical`, `_tilde` | fiel |

## Escopo

Os resultados do artigo para `s ≤ 1/p` (Teorema 3.1, itens (ii) e (iii), Teorema 3.2 nesse regime, Lema 4.8 a Teorema 4.10 e Proposição 5.6) **não têm contrapartida em Lean**. Esta auditoria cobre apenas o regime `1/p < s < 2`.

## Achados

1. **Mensurabilidade das famílias (Conj. 2)**: as famílias do texto são subconjuntos de `C([0,1])`, logo mensuráveis; a exigência Lean não enfraquece o teorema para elas. **Aplicado no artigo** (apêndice, §Representação dos objetos e dos teoremas): a frase agora explica que a exigência não restringe o enunciado.
2. **`conj1_tilde` e `conj2_tilde`**: o enunciado Lean agora exige `s<2` (hipótese `hs2`), igualando o artigo, que define `B^s_{p,q}` por diferenças de ordem dois apenas para `0<s<2` (`lp:eq:besov-p`). Os lemas internos `_of_J` continuam sem essa hipótese. Estender a definição para `s≥2` não é adequado: a ordem dois não caracteriza smoothness acima de 2.
3. **`J_p` como usada nas reduções** é mais fraca que o texto (constantes dependentes de `f`), e `R` é o `toReal` do supremo pontual do representante dado. Já documentado no apêndice ("constantes que podem depender de `f`"). Um detalhe a acrescentar: para um representante com supremo pontual infinito, `toReal` dá `R=0`; a afirmação continua verdadeira porque `C_1` pode depender de `f`.
4. **Identidade do núcleo com a projeção ortogonal**: formalizada em `Formalizacao/Kernel.lean`.
5. **Escopo dos enunciados Lean**: funções mensuráveis, não classes de `L^p`. Equivalente para classes, já documentado no artigo.

## Pendências desta auditoria

- Aplicadas: (1) no artigo; (2) no Lean (`hs2 : s < 2`). (3) e (5) já estão documentadas no artigo; (4) está formalizada.
- Esta auditoria não substitui uma leitura humana de ponta a ponta do texto.
