# F5 — Teorema 5.2 em Lean 4

A etapa começa no checkpoint F4 `8193ad3dd898126ae74ae62388f72ed27a76c19a`, na branch
`formalizacao-teorema-5-2`. A declaração
[`FormalizacaoMinimax.minimax_nh`](../lean4/formalizacao/Formalizacao/MinimaxFinal.lean)
demonstra as duas desigualdades de `lp:thm:minimax-nh` sob `1 ≤ p`, `0 < s < 2`
e `0 < q ≤ ∞`. Os orçamentos são naturais `N,H ≥ 2`, e as duas constantes positivas
são escolhidas antes de ambos.

## Cota inferior e composição

`lower_bound_NH` reutiliza `leaf_floor_const` para obter `c_N N^(-s)`.
O piso de altura é obtido por `dfun_slope_floor` abaixo de `1/p`,
`dfun_geometric_floor` no intervalo fechado `[1/p,1]` e `dfun_arithmetic_floor`
acima de 1. As identidades de `aPS` convertem os três pisos em
`c_H H^(-s/aPS p s)`. No último regime, `aPS p s = s`, e o piso é exatamente
`(1/2) H^(-1)`.

Cada ponte da F2 introduz seu próprio alvo no supremo `Dfun`. Assim o mesmo supremo
domina o máximo dos dois pisos, mesmo quando os alvos que os produzem são diferentes.
O máximo é pelo menos a metade da soma. A constante resultante é
`min(c_N,c_H)/2 > 0`. A composição final aplica `upper_bound_NH` e reúne os
dois lados para os mesmos orçamentos.

| Regime | Expoente de altura `aPS p s` | Piso de altura | Construção superior |
|---|---|---|---|
| `0 < s < 1/p` | `1 + 1/p − s` | Inclinação | Cota uniforme por escala com `κ = 0`. |
| `1/p < s ≤ 1` | `1` | Geométrico | Cota uniforme por escala com `κ = 0`. |
| `1 < s < 2` | `s` | Aritmético | Cota uniforme por escala com `κ = 0`. |
| `s = 1/p`, `p > 1` | `1` | Geométrico | `critical_upper_dyadic`. |
| `p = s = 1` | `1` | Geométrico | `l1_linear_height`. |

Todos os regimes valem para `0 < q ≤ ∞`. O extremo `s = 1` cai no segundo ou no
último regime da tabela, conforme `p > 1` ou `p = 1`.

## Correspondência com o LaTeX

O enunciado usa exatamente `Dfun` da F2 e a mesma bola unitária de Besov em Lᵖ.
A ordem dos quantificadores coincide com o manuscrito. Lean escreve `p,s` em `ℝ`,
`q` e os valores do melhor erro e do supremo em `ℝ≥0∞`, e usa `ENNReal.ofReal`
para inserir as cotas reais. A definição de `Dfun` quantifica sobre representantes
mensuráveis. No piso de folhas, a F2 fixa o bump `φB` e controla o módulo por
sobreposição local. Na cota superior, a F4 instancia a conclusão pontual da agenda
uniforme fora da diagonal, e controla diretamente o erro em Lᵖ nos pontos críticos.
Essas escolhas preservam o funcional, os expoentes e a faixa de parâmetros.

A entrada M5 do mapa liga o rótulo `lp:thm:minimax-nh` ao enunciado completo e às
duas cotas. As entradas M2–M4 apontam para os resultados certificados da F2 e da F3
reutilizados na prova.

## Verificações

- `lake build Formalizacao` passou com 8140 jobs. O build reportou avisos preexistentes.
- `python3 -B -m unittest discover -s testes -v` passou com 9 testes.
- [`Minimax52.lean`](../testes/Minimax52.lean) verifica ambos os lados em seis pares
  `(p,s)`. Cada par é instanciado com `q = 1/2` e `q = ∞`. Os pares são
  `(2,1/4)`, `(2,3/4)`, `(2,1)`, `(2,3/2)`, `(2,1/2)` e `(1,1)`.
  Os testes conferem os expoentes numéricos da altura e incluem o limiar diádico
  `X = 2` e o aumento simultâneo dos dois orçamentos.
- As auditorias transitivas de `lower_bound_NH` e `minimax_nh` retornaram somente
  `propext`, `Classical.choice` e `Quot.sound`. A varredura dos arquivos novos
  encontrou zero ocorrências de `sorry`, `admit`, `axiom` ou `opaque`. A execução
  integral de `Auditoria.lean` no checkpoint F4 coincidiu byte a byte com suas
  237 linhas de registro. As duas consultas F5 foram executadas sobre o módulo
  final e acrescentadas ao registro, que ficou com 239 linhas e zero `sorryAx`.
- `python3 -B mapas/verificar_mapa.py` conferiu 64 entradas e 267 referências a nomes
  Lean. O mapa gerado está atualizado.

A F6 fica reservada à reprodução independente do build, dos testes e da auditoria de
axiomas, e à revisão semântica item a item entre o enunciado Lean e o manuscrito
congelado. A formalização aqui registrada é a entrega de F4 e F5.
