# Auditoria de fidelidade: enunciados Lean × texto de `conjecturas_lp.tex`

Escopo da auditoria de base: definições (§2) e enunciados dos resultados principais (§§3–6) na numeração anterior à Etapa 2. A atualização abaixo usa os rótulos estáveis do manuscrito. Veredito por item: **fiel** (mesmo conteúdo), **diferença documentada**
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

## Escopo

Os resultados para `s ≤ 1/p` (Teorema 3.1, itens (ii) e (iii), Teorema 3.2 nesse regime, Lema 4.8, Lema 4.9, Teorema 4.10 e Proposições 5.7 e 5.8) estão formalizados em `Formalizacao/Low*.lean`. A Seção 6 (cotas uniformes, piso aritmético, bits e agendas de log iterado) está formalizada em `UnifSup`, `UnifTheorem`, `ArithmeticFloor`, `BinaryBudget`, `RegularSchedules`, `IteratedSchedules` e `LogLogSchedules`. A correspondência está em `MAPA_TEX_LEAN.md`.

Os enunciados da Seção 6 que envolvem `ω_2` exigem `s < 2`, como no artigo (`uniform_besov_ball`, `uniform_rate_bits`, `conj1_loglog`, `conj2_loglog`, `conj2_approx_loglog`, `uniform_loglog_ball`).

| Resultado | Texto | Lean | Veredito |
|---|---|---|---|
| Lema 4.8 (nodal sem saltos) | `Q = 2^e ≥ n`, `H ≥ 8(M+1)Q`, erro `≤ 1/(2Q)` | `nodal_tree_gen`, `lp_jackson_low_core` | fiel |
| Lema 4.9 (cota em sup) | `‖Q_n f‖_∞ ≤ C_0 S Λ_n`, `C_0 = C_0(p,s,q)` | `lam_bound`: `∃ K ≥ 1` (depende de `f`) com `|λ_j(f)| ≤ K Λ_r` | **diferença documentada** (constante dependente de `f`; basta para os teoremas) |
| Teorema 4.10 (Jackson `s ≤ 1/p`) | `H ≥ 8 C_0 (S+1) Λ_n Q` | `jackson_low`: `H ≥ 8 (K Λ_r + 1) 2^e`, `C_W`, `K` dependentes de `f` | **diferença documentada** (mesma razão) |
| Prop. 5.7 (transferência) | deslocamento `d` com `K Λ_n Q(n) ≤ H(dn)` | `besov_subset_stratum_low` com `hshift`, `m = 0` ou `mDiag κ` | fiel |
| Teorema 3.1 (ii) | `0 < s < 1/p`, `Ĥ_s` | `conj1_low` (`s < 1/p`, sem exigir `s > 0`), agenda `Hsk (1 + 1/p - s) 0` | **mais geral** em `s` |
| Teorema 3.1 (iii) | `s = 1/p`, `Ĥ_{q,κ}`, `κ > 1/q` se `p = 1`, `q < ∞` | `conj1_diag`, agenda `Hsk 1 (thetaQ q + κ)` | fiel |
| Teorema 3.2 (`s ≤ 1/p`) | família aninhada, `c ≥ 1` | `conj2_low`, `conj2_diag` | fiel (famílias mensuráveis, como no regime `s > 1/p`) |
| Teorema 3.3 (estabilidade aproximada) | inclusão aproximada em `L^p`, `(2^{rs}ε_{2^r}) ∈ ℓ^q` | `Conj2ApproxStability`, `conj2_approx_endpoint`/`_subcritical`/`_critical`/`_tilde` (`s > 1/p`), `conj2_approx_low`/`_diag` (`s ≤ 1/p`) | fiel (tolerância `ε : ℕ → ℝ≥0∞`; somabilidade como premissa) |

## Cotas uniformes e agendas de altura (seção 6)

| Resultado | Correspondência e escopo |
|---|---|
| 6.1–6.3 | `besovNorm` mede a bola de raio `B`. `uniform_besov_ball` escolhe as constantes de altura e de Whitney antes de `κ`, do raio e da função. A norma de realização reindexa as escalas a partir de `r = 1`. |
| 6.4 | `uniform_quantWeight_zero_not_lt_top` prova divergência para `q` finito, `s ≥ 1` e `κ = 0`. O teto da potência de dois mantém o peso afastado de zero. |
| 6.5–6.7 | O piso é provado primeiro em `L¹` pela média afim em cada folha. A monotonia de `Lᵖ` na medida de probabilidade dá o piso com a mesma constante. A necessidade de altura é por escala e uniforme na bola. |
| 6.8–6.9 | A forma da árvore determina os endereços. As magnitudes têm `⌈log₂(H+1)⌉` bits. A cardinalidade é limitada por `2^L`, com `L = 4N(c_H + 1)`. |
| 6.10 | Estado em `9951091`: a ordem da entropia métrica da bola de Besov era citada como resultado externo. Ver «Atualização posterior». |
| 6.11–6.13 | A condensação de Cauchy dá as duas equivalências do critério e reduz as séries de Bertrand a uma série de potências. O limiar `γq = 1` é divergente no critério. A igualdade com log-log inclui a diagonal `p = s = 1`, e a estabilidade no regime `s > 1/p` usa as duas transferências existentes. |

## Achados

1. **Mensurabilidade das famílias (Conj. 2)**: as famílias do texto são subconjuntos de `C([0,1])`, logo mensuráveis; a exigência Lean não enfraquece o teorema para elas. **Aplicado no artigo** (apêndice, §Representação dos objetos e dos teoremas): a frase agora explica que a exigência não restringe o enunciado.
2. **`conj1_tilde` e `conj2_tilde`**: o enunciado Lean agora exige `s<2` (hipótese `hs2`), igualando o artigo, que define `B^s_{p,q}` por diferenças de ordem dois apenas para `0<s<2` (`lp:eq:besov-p`). Os lemas internos `_of_J` continuam sem essa hipótese. Estender a definição para `s≥2` não é adequado: a ordem dois não caracteriza smoothness acima de 2.
3. **`J_p` como usada nas reduções** é mais fraca que o texto (constantes dependentes de `f`), e `R` é o `toReal` do supremo pontual do representante dado. Já documentado no apêndice ("constantes que podem depender de `f`"). Um detalhe a acrescentar: para um representante com supremo pontual infinito, `toReal` dá `R=0`; a afirmação continua verdadeira porque `C_1` pode depender de `f`.
4. **Identidade do núcleo com a projeção ortogonal**: formalizada em `Formalizacao/Kernel.lean`.
5. **Escopo dos enunciados Lean**: funções mensuráveis, não classes de `L^p`. Equivalente para classes, já documentado no artigo.

## Pendências desta auditoria

- Aplicadas: (1) no artigo; (2) no Lean (`hs2 : s < 2`). (3) e (5) já estão documentadas no artigo; (4) está formalizada.
- Esta auditoria não substitui uma leitura humana de ponta a ponta do texto.

## Atualização posterior ao commit `9951091`

- **Cota inferior de entropia e de bits.** `lp:lem:packing`, `lp:prop:entropy-lower` e `lp:cor:bits-lower` são demonstrados no artigo a partir da definição de Besov por diferenças de segunda ordem. A equivalência com wavelets não é necessária para essa cota inferior. A cota superior da entropia não é afirmada.
- **Cobertura Lean.** Esses resultados **não estão formalizados**. O mapa os lista como «Demonstrado no texto (sem formalização Lean)», sem declarações Lean. As compilações e a auditoria axiomática dos módulos existentes não os certificam.
- **Whitney.** O texto usa `m=min(k,n−2)`, igual à formalização (`Jcell`, `Iset`).


## Etapa 2 — lei minimax e altura crítica

Esta tabela registra a cobertura anterior às etapas F2–F6. A atualização abaixo descreve a certificação posterior.

| Rótulo | Escopo efetivamente coberto em Lean | Prova analítica da edição de 21 de novembro de 2026 |
|---|---|---|
| `lp:prop:geom-floor` | `geometric_floor` e `terminal_affine` cobrem o piso e a folha terminal. | A prova agora explicita o campo `m+1 = 2^k` da altura e trata o zero. |
| `lp:eq:nikolskii` | `kernel_is_affine_projection` e `abs_integral_kernel_le` sustentam reprodução e estimativa local. | A constante 4 resulta da aplicação a uma função afim, seguida da fórmula da inclinação. |
| `lp:lem:leaf-budget-floor` | `L1_affine_lower` sustenta o teste contra afins em uma célula. | A normalização e a contagem das células livres de fronteiras são analíticas. |
| `lp:thm:minimax-nh` | Pisos aritmético, geométrico e de inclinação. Cotas de quase-interpolação e quantização de denominador comum. | A equivalência minimax conjunta é analítica. |
| `lp:lem:nodal-variable-height` | As declarações anteriores de quantização operam com denominador comum na malha. | A escolha de denominadores por nó e o teste no ponto $p=s=1$ são analíticos. |
| `lp:cor:minimax-realization` | `bestError_le_realP` e `realP_le_bestError_add` cobrem a comparação em cada escala. | A passagem ao supremo e a equivalência minimax são analíticas. |
| `lp:thm:critical-linear` | `critical_approx` e `critical_level` supõem controle do módulo sem parâmetro $q$. `critical_lq`, `critical_rate` e `critical_radius_ball_and_inclusion` exigem `q ≠ ⊤`. | A estimativa sequencial para $q=\infty$ e a versão por bola nesse caso são analíticas. |
| `lp:thm:critical-fixed-agenda` | `stratum_subset_besov_conn` cobre a inclusão inversa universal. | O deslocamento a partir de $H_B$ e a igualdade sob $H_*$ são analíticos. |
| `lp:prop:critical-radius-growth` | A cota por bola para $q$ finito sob $H_B$ oferece apoio parcial. | O crescimento ótimo do raio sob $H_*$ e a obstrução por constantes são analíticos. |

`nodal_jump` aceita as cotas de inclinação em cada célula como hipóteses e independe de $p$. A edição integra a dedução dessas hipóteses para $p=1$ em `lp:lem:critical-jump`. A estimativa média de projeção e a aplicação ao quantizador por nó de `lp:prop:l1-linear-height` são novas provas analíticas. A igualdade em $B^1_{1,\infty}$ com agenda fixa também é analítica.

## Atualização F6 — Teorema 5.2

No commit `19c85be8bd08098b4a8c6d0452e755b5e3683be7`, `FormalizacaoMinimax.minimax_nh` formaliza as duas cotas do melhor erro minimax com orçamentos independentes. A auditoria independente atribuiu parecer A ao enunciado completo. O fechamento inclui `nodal_variable_height`, `critical_upper_dyadic` e `l1_linear_height`, que dão a quantização por nó e o controle de altura linear por escala nos regimes críticos. A entrada E1 do mapa registra o apoio parcial ao item (i) do lema de empacotamento pelo caso na bola unitária com bits todos iguais a 1. A família de Hamming, as cotas inferiores de entropia e bits e os resultados globais por somabilidade requerem rastreabilidade própria. [Relatório F6](../auditorias/RELATORIO_F6_CERTIFICACAO_FINAL.md) · [Mapa atualizado](MAPA_TEX_LEAN.md)
