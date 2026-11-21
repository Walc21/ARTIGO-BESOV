# Pendências de revisão final — decorrentes da auditoria E1/E2

Este arquivo acompanha `RELATORIO_E1_E2_CONCLUSIVO_4_FONTES.md`, preservado sem alterações. Registra pontos do relatório que devem ser reformulados ou conferidos antes de qualquer redação definitiva (E5/E6). Nenhum manuscrito, PDF, bibliografia, Lean ou teste foi modificado.

Referência: branch `pesquisa-minimax-altura`, base `a8c52ef5b49b404aa43e150cfc223733934e5f4d`.

## 1. Cota de codificação `O(N log N)` e a perda de `log N`

**Ponto.** O relatório (seções 3, 9 e P5) afirma que a biblioteca de altura "perde um fator `log N`" em relação à ordem ótima de bits. Isso excede o que foi demonstrado.

**O que está demonstrado.** A Proposição `lp:prop:bits` dá uma cota superior de `4N(c_H+1)` bits para descrever os elementos de `Σ_{N,H}` com um código de comprimento fixo por campo. Com `H≍N^{a}`, isso é `O(N log N)`. A cota inferior de entropia dá `L ≥ c_5N−1`. A diferença entre as duas cotas é um fator `log N`.

**O que não está demonstrado.** Que *toda* codificação da biblioteca necessariamente custe `Ω(N log N)` bits. Uma cota superior de código não é uma cota inferior de custo. Não foi investigado se um código de comprimento variável (por exemplo, com endereços diferenciais, como o de Kerkyacharian–Picard) descreve `Σ_{N,H}` com `O(N)` bits, nem se `log_2|Σ_{N,H}|` é de fato da ordem de `N log N` (a contagem de cardinalidade da biblioteca não foi feita em sentido inferior).

**Reformulação a fazer.** Escrever que a codificação de comprimento fixo da Prop. `lp:prop:bits` fornece `O(N log N)` bits, enquanto a cota de entropia fornece `Ω(N)`; que a lacuna de `log N` entre as duas cotas é uma limitação dessa codificação, e que não se afirma que ela seja intrínseca à biblioteca.

## 2. Spline de DeVore–Popov e a biblioteca racional

**Ponto.** O relatório (seção 8, linha da tabela de DeVore–Popov, e a linha correspondente da matriz na seção 13) usa a notação `Σ_{n,∞} ⊃ T_k` e fala em "inclusão". Não afirmar inclusão exata.

**Razão.** `T_k(f)=Q_k(S_k(f))` (DeVore–Popov, Teor. 4.5) tem valores nodais reais. Os segmentos da biblioteca têm valor central e inclinação racionais, com altura `≤H`, inclinação não nula e endereço da folha terminal limitado. Um elemento de `T_k` não pertence a `Σ_{n,H}` em geral.

**Reformulação a fazer.** Dizer que o termo `N^{-s}` da cota superior segue do Teorema 4.5 *após racionalização* dos valores nodais e controle das alturas (valor central, inclinação e endereço), e que essa racionalização é o conteúdo dos lemas do manuscrito (`lp:lem:nodal-general`, `lp:lem:nodal-jump`, `lp:lem:nodal-variable-height`). A relação é de dedução com um passo adicional, não de inclusão de famílias.

## 3. Elbrächter et al.: mesmo calibre aritmético contra qualquer quantização

**Ponto.** Em vários trechos do relatório (resumo executivo, P1, seção 4 e a linha de Elbrächter na seção 8) a ausência de "restrição aritmética" ou de "parâmetro de altura" pode ser lida como ausência de qualquer quantização. Isso não é o caso.

**Distinção a manter.**
- Elbrächter et al. controlam quantização de pesos: pesos `(m,ε)`-quantizados, com precisão que cresce como uma potência de `log ε⁻¹`, e conectividade `M(Φ)`. A quantização existe e é central ao resultado.
- O manuscrito controla um calibre aritmético diferente: altura `max{|a|,b}` dos valores centrais e das inclinações racionais, mais o endereço diádico da folha, em funções contínuas com `≤N` folhas.
- Cohen et al. e Kerkyacharian–Picard também quantizam coeficientes (por planos de bits ou por limiar `λ`).

**Reformulação a fazer.** Substituir "sem restrição aritmética" por "sem o mesmo calibre aritmético" onde se refere a esses trabalhos, e especificar o recurso que cada um controla. Manter a conclusão de que não há redução demonstrada entre os modelos, sem sugerir que Elbrächter et al. ignorem a quantização.

## 4. Referências a conferir: Cohen et al. e Elbrächter et al.

Conferir contra as fontes (PDF ou página do periódico) antes de incluir em `conjecturas_lp_referencias.tex`:

| Fonte | Dados registrados no relatório | A conferir |
|---|---|---|
| Cohen, Dahmen, Daubechies, DeVore | *Appl. Comput. Harmon. Anal.* 11(2), 2001, p. 192–226, DOI 10.1006/acha.2001.0336. PDF examinado: cabeçalho `11, 192–226 (2001)` e `doi:10.1006/acha.2001.0336` conferidos. | Número do fascículo (2), mês, chave de citação `lp-cohen2001` (proposta) |
| Elbrächter, Perekrestenko, Grohs, Bölcskei | *IEEE Trans. Inf. Theory* 67(5), 2021, a partir da p. 2581; arXiv:1901.02220. | Página final, DOI, mês, chave de citação `lp-elbrachter2021` (proposta). O relatório deixa a página final em aberto. |

Chaves já presentes e que não exigem nova entrada: `artigo_2-devorepopov1988`, `lp-kerkyacharianpicard2003`, `lp-yang2024`, `lp-siegel2023`, `lp-oliveiravol`. Conferir também se Ou–Schenkel–Bölcskei (arXiv:2405.01952) será citado e, se for, criar a entrada.

Os quatro PDFs externos analisados (Yang, Cohen et al., DeVore–Popov, Kerkyacharian–Picard) **não foram adicionados ao repositório**. Suas referências estão na seção 2 e na seção 15 do relatório.

## 5. Lei conjunta `C²` e o Teorema 5.2

**Ponto.** O relatório (seção 11) observa que, em `s=2`, a fórmula `N^{-s}+H^{-s/a}` com `a=s` dá `N^{-2}+H^{-1}`. Essa observação é uma coincidência de forma, não uma identificação.

**Registro a manter.** A lei conjunta `E_{N,H}(F_{R,M}) ≍ N^{-2}+H^{-1}`, com `F_{R,M}={f∈C²[0,1]:‖f‖∞≤R,‖f''‖∞≤M}`, é consequência de resultados anteriores da Biblioteca Determinística (`artigo_2:thm:joint-budget`, parte dyadic) combinados com um piso quadrático elementar e o piso aritmético. A classe `C²` não é a classe `B^s_{p,q}` do Teorema 5.2, cuja hipótese é `0<s<2`.

**Reformulação a fazer.** Atribuir a lei `C²` à Parte II e a seus pisos elementares. Não descrevê-la como caso `s=2` do Teorema 5.2 e não usar a fórmula do Teorema 5.2 como enunciado do caso `C²`. Se o manuscrito mencionar a coincidência de forma, apresentá-la como observação, com a ressalva de que as classes são diferentes.

## Estado do repositório no momento deste registro

- Relatórios E3/E4 e mapas de formalização preservados, sem alterações: `RELATORIO_CORRECOES_E3_E4.md`, `RELATORIO_VALIDACAO_ETAPA_2.md`, `RELATORIO_VALIDACAO_INTEGRACAO.md`, `AUDITORIA_INTEGRACAO.md`, `mapas/MAPA_TEX_LEAN.md`, `mapas/AUDITORIA_FIDELIDADE.md`, `mapas/dados/mapa_lp.json`, `mapas/gerar_mapa.py`, `mapas/verificar_mapa.py`.
- Manuscritos LaTeX, PDFs, bibliografia, Lean e testes: não modificados.

---

## Status de resolução (Etapa 4B.4, integração E1/E2)

As cinco pendências acima foram tratadas nas três edições (a ABNT compartilha a fonte portuguesa) e na bibliografia. O histórico acima foi preservado. Detalhes em `RELATORIO_INTEGRACAO_E1_E2.md`.

| # | Pendência | Estado | Onde |
|---|---|---|---|
| 1 | `O(N log N)` contra `Ω(N)` de bits | **Resolvida no manuscrito** | PT 1392 / EN 1362 (Considerações finais): a diferença é a lacuna entre a cota superior do código de comprimento fixo (`lp:prop:bits`) e a cota inferior de entropia; o texto não afirma `Ω(N log N)` em toda codificação. |
| 2 | Spline de DeVore–Popov e biblioteca racional | **Resolvida no manuscrito** | PT 55 / EN 26: a estimativa direta é o ponto de partida do termo `N^{-s}`; a passagem às montagens racionais exige racionalizar valores nodais e controlar alturas. Nenhuma inclusão é afirmada. |
| 3 | Mesmo calibre aritmético contra qualquer quantização | **Resolvida no manuscrito** | PT 55 / EN 26: Cohen et al., Birman–Solomyak e Kerkyacharian–Picard "quantizam coeficientes e medem o custo em bits"; Siegel e Yang usam parâmetros reais; Elbrächter et al. usam pesos quantizados em precisão `~ (log ε⁻¹)^k`, em `L^2`. Os modelos "diferem" e nenhuma redução é estabelecida. |
| 4 | Referências de Cohen et al. e Elbrächter et al. | **Resolvida, com duas conferências abertas** | Chaves `lp-cohen2001`, `lp-elbrachter2021` (e `lp-birmansolomyak1967`) em `conjecturas_lp_citacoes.tex` e `conjecturas_lp_referencias.tex`. Cohen: v. 11, n. 2, p. 192–226, DOI do cabeçalho do PDF. Elbrächter: v. 67, n. 5, p. 2581–2623 (registro do periódico), arXiv 1901.02220; **DOI não verificado e não incluído**. Birman–Solomyak: dados conforme citados por Cohen et al. e Kerkyacharian–Picard; **original não consultado**. |
| 5 | Lei conjunta `C²` | **Resolvida no manuscrito** | PT 55 / EN 26: atribuída à Parte II e aos pisos aritmético e quadrático; "não se confunde com o caso `s=2`" do Teorema 5.2, cuja hipótese é `0<s<2`. |

**Itens ainda abertos:** (i) DOI de Elbrächter et al.; (ii) páginas de Birman–Solomyak no original; (iii) a lei conjunta `C²` é afirmada no texto como consequência da Parte II, mas a dedução (cota superior para `(N,H)` independentes e piso quadrático) consta só em `RELATORIO_E1_E2_CONCLUSIVO_4_FONTES.md`, seção 11, e não no manuscrito; (iv) o relatório preservado `RELATORIO_E1_E2_CONCLUSIVO_4_FONTES.md` mantém, por decisão, as formulações originais criticadas nas pendências 1, 2, 3 e 5; (v) os PDFs rastreados não foram regenerados.

---

## Atualização (Etapa 5, E5/E6)

Itens abertos ao final da integração E1/E2 e seu estado:

| Item aberto | Estado | Como foi tratado |
|---|---|---|
| (i) DOI de Elbrächter et al. | **Fechado** | DOI `10.1109/TIT.2021.3062161`, v. 67, n. 5, p. 2581–2623, 2021, conferido em registro do Crossref; incluído na entrada `lp-elbrachter2021`. |
| (ii) Páginas de Birman–Solomyak | **Fechado, com ressalva** | O registro do Crossref dá *Mathematics of the USSR-Sbornik*, v. 2, n. 3, p. 295–317, 1967, DOI `10.1070/SM1967v002n03ABEH002343`. As páginas 295–317 são, portanto, as da tradução inglesa. A entrada `lp-birmansolomyak1967` passou a citar essa tradução. Os dados do original russo (*Mat. Sb.* 73) não foram confirmados e não foram incluídos. |
| (iii) Dedução da lei `C²` fora do manuscrito | **Fechado** | Nova `lp:obs:c2-joint` (Seção 5, após `lp:obs:floor-closure`) traz a dedução curta, atribui à Parte II só o que ela demonstra (montagem de `n` folhas, erro `≤(M+4)/(8n²)`, altura `≤C_Hn²`) e declara que a lei não é o caso `s=2` do Teorema 5.2. |
| (iv) Relatório de auditoria preservado com formulações originais | Mantido por decisão | `RELATORIO_E1_E2_CONCLUSIVO_4_FONTES.md` não foi alterado. |
| (v) PDFs rastreados desatualizados | **Fechado** | Os três PDFs foram regenerados. |

Pendências novas ou que permanecem: ver `RELATORIO_E5_E6_CONSOLIDACAO.md`, seção 9.
