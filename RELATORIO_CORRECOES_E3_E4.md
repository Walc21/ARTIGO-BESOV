# ARTIGO-BESOV — Etapa 4A

Os seis itens de E3 e E4 foram corrigidos e verificados nas edições em português, inglês e ABNT. A transferência agora usa o domínio $L^p$ do módulo, as duas modalidades de orçamento têm domínios explícitos e a prova do empacotamento usa suportes compactos no interior das células. A cota de bits conserva $L\ge c_5N-1$ com decodificadores que admitem colisões. A observação de entropia identifica o papel do corte de escala e a cobertura trivial para $\varepsilon\ge B$. Os seis resultados centrais solicitados conservaram enunciados e provas.

## A. Identificação

- Repositório `Walc21/ARTIGO-BESOV`, branch `pesquisa-minimax-altura`.
- SHA inicial e auditado `4aa477cb35836003bf16deaec6d72dd769ba986a`. A árvore inicial estava limpa e o diff inicial contra o commit auditado era vazio.
- O SHA final é o do commit que introduz este relatório junto com as correções. O comando `git log --diff-filter=A -1 --format=%H -- RELATORIO_CORRECOES_E3_E4.md` identifica esse commit mesmo após novos avanços na branch.
- O diff final abrange `conjecturas_lp.tex`, `conjecturas_lp_en.tex`, os três PDFs versionados, `mapas/dados/mapa_lp.json`, `mapas/MAPA_TEX_LEAN.md` e `testes/test_edicoes.py`. Este relatório é o único arquivo novo.
- A revisão usou os seis apontamentos reproduzidos no pedido da Etapa 4A e as fontes do commit auditado. O parecer completo da Etapa 3 como arquivo separado não foi localizado na árvore nem no histórico local.

## B. Matriz de correções

As linhas referem-se ao rótulo nas fontes PT e EN. A edição ABNT carrega a fonte PT.

| ID | Localização | Formulação anterior | Formulação corrigida | Justificativa e impacto | Estado |
|---|---|---|---|---|---|
| E3.1 | 5.3, `lp:prop:transfer` · [PT 922](conjecturas_lp.tex#L922) · [EN 893](conjecturas_lp_en.tex#L893) | Alvo e membros da família meramente mensuráveis, com passagem direta ao ínfimo. | $N\ge2$, $f\in L^p$, $G_N\subseteq L^p$ e módulo com a notação da definição. A prova trata a família vazia e usa candidatos a distância $\delta$ do ínfimo. | Cada custo é finito na família não vazia. A constante $5$ e as aplicações do artigo são preservadas. | Corrigido e verificado |
| E3.2 | 4.2, `lp:cor:floor` · [PT 691](conjecturas_lp.tex#L691) · [EN 662](conjecturas_lp_en.tex#L662) | $s>0$ para a bola de Besov. A observação seguinte usava $s\ge1$ e escrevia $n=2^r$. | $0<s<2$, com os índices da bola explícitos e $H(N)\ge2$ ligado ao $N\ge2$ da hipótese. Em `lp:obs:floor`, $1\le s<2$, $B\ge1$ e $n=2^r\ge2$. | A faixa é a da definição. O alvo constante mantém $H(N)\ge N^s/(2C)$ e a observação explicita as hipóteses da estimativa uniforme citada. | Corrigido e verificado |
| E3.3 | 4.7, `lp:cor:joint-necessity` · [PT 779](conjecturas_lp.tex#L779) · [EN 750](conjecturas_lp_en.tex#L750) | Uma hipótese de $N\ge1$ era compartilhada entre erro e realização. | O melhor erro continua para $N\ge1$. A variante quantifica sobre a mesma bola e usa $R_{N,H(N)}(f)_p$ para $N\ge2$. Os dois domínios constam junto às definições. | A biblioteca de uma folha é admissível para o erro, e a realização segue a convenção de `lp:def:realization`. Os três pisos conservam as constantes. | Corrigido e verificado |
| E4.1 | 4.8, `lp:lem:packing` · [PT 792](conjecturas_lp.tex#L792) · [EN 763](conjecturas_lp_en.tex#L763) | Suporte identificado com a célula aberta e $m\in\mathbb N$ na construção. | $m\ge1$ explícito, extensão suave por zero e inclusão compacta no interior. A prova identifica $M_\varphi$ na estimativa e justifica o expoente combinatório por uma desigualdade inteira exata. | A inclusão garante disjunção. A mudança de variável, a fórmula de Hamming, $C_1,C_2,K_{s,q}$ e a cota $2^{m/6}$ permanecem válidas. | Corrigido e verificado |
| E4.2 | 8.4, `lp:cor:bits-lower` · [PT 1367](conjecturas_lp.tex#L1367) · [EN 1337](conjecturas_lp_en.tex#L1337) | A contagem $2^{L+1}-1$ era atribuída aos valores de $D$. | $L\ge0$ inteiro. Há $2^{L+1}-1$ palavras, incluindo a vazia, e a imagem tem no máximo essa cardinalidade. | As bolas centradas na imagem cobrem a classe. A dedução preserva $c_5$ e o termo $-1$ para códigos de comprimento máximo $L$. | Corrigido e verificado |
| E4.3 | 8.5, `lp:obs:entropy` · [PT 1383](conjecturas_lp.tex#L1383) · [EN 1353](conjecturas_lp_en.tex#L1353) | O corte específico $\varepsilon_0B$ era chamado indispensável. A notação da bola fora introduzida para $B\ge1$. | O corte é suficiente para a construção. A observação distingue o intervalo enunciado, as escalas intermediárias e a cobertura com centro zero. A notação da bola admite $B>0$, como requerido na Proposição 8.3 e no Corolário 8.4. | O impedimento à cota positiva aparece em $\varepsilon\ge B$. Os enunciados da cota de entropia e da estimativa uniforme conservam seus respectivos domínios. | Corrigido e verificado |

## C. Verificação matemática

### E3.1 · Transferência, domínio e ínfimo

Em `lp:eq:modulus-p`, o módulo de $u\in L^p$ é finito, pois a mudança de variável em cada translação e Minkowski dão $\omega_2(u,t)_p\le4\|u\|_p$. Isso vale para representantes de $L^p$ porque cada translação preserva conjuntos nulos. Em `lp:def:realization`, o domínio pede $f\in L^p$ e uma família de subconjuntos de $L^p$ indexada por $N\ge2$. A convenção de valores estendidos é necessária para o ínfimo da família vazia. Uma extensão a funções mensuráveis seria possível usando normas estendidas em todas as definições e a desigualdade triangular nesse codomínio. As aplicações utilizam alvos de Besov e aproximantes contínuos, de modo que o domínio já definido basta.

Para $G_N=\varnothing$, vale $e_N(f)=\mathscr R_N(f)=+\infty$ e o extremo direito também é $+\infty$. Para $G_N\ne\varnothing$, cada custo é real não negativo e os dois ínfimos são finitos. A inclusão de um termo não negativo em cada custo dá $e_N\le\mathscr R_N$. Pelo Lema 2.1, aplicado a $g=f+(g-f)$ no passo $N^{-1}>0$,

$$
\|f-g\|_p+\omega_2(g,N^{-1})_p
\le \omega_2(f,N^{-1})_p+5\|f-g\|_p.
$$

Para qualquer $\delta>0$, a definição do ínfimo fornece $g_\delta\in G_N$ com $\|f-g_\delta\|_p<e_N(f)+\delta$. O custo desse candidato limita $\mathscr R_N$ por cima. Tomar $\delta\downarrow0$ preserva a desigualdade, inclusive quando nenhum candidato atinge $e_N$.

**Dependências.** `lp:thm:critical-linear` usa alvos da bola e candidatos contínuos em $n=2^r\ge2$. `lp:cor:minimax-realization` usa $N,H\ge2$ e $\Sigma_{N,H}\subseteq C([0,1])\subset L^p$. A observação `lp:obs:critical-scope` usa a mesma construção em escalas diádicas $n\ge2$ no ponto $p=s=1$. `lp:cor:joint-necessity` usa explicitamente o mesmo domínio na variante de realização.

### E3.2 · Faixa de suavidade

O alvo $f\equiv1/(2H(N))$ tem módulo zero para todo passo e norma $L^p$ igual a $1/(2H(N))\le1/4$. Logo pertence à bola unitária no domínio de `lp:eq:besov-p`. O piso de `lp:prop:floor` vale candidato por candidato. Somar o módulo do candidato preserva o piso, e tomar o ínfimo e aplicar a taxa uniforme ao alvo dá $1/(2H(N))\le CN^{-s}$, equivalente a $H(N)\ge N^s/(2C)$.

O argumento com a função constante é independente do limiar superior de $s$. O limiar vem da definição do espaço, que usa segundas diferenças em $0<s<2$. O uso posterior direto, em `lp:obs:floor`, herda essa faixa da estimativa de `lp:thm:uniform`. A mesma prova fornece a estimativa por escala com $\kappa=0$, $B\ge1$ e $n\ge2$. A condição de admissibilidade adicional daquele teorema incide na estimativa de sequência.

### E3.3 · Uma folha e realização

A biblioteca $\Sigma_{N,H}$ contém zero e admite representações com até $N$ folhas. Em $N=1$, qualquer candidato não nulo usa a célula raiz. O argumento do centro da folha de `lp:prop:floor`, o da folha terminal direita de `lp:prop:geom-floor` e a cota de Lipschitz de `lp:prop:slope-floor` se aplicam a essa classe. Cada testemunha pertence à bola unitária. Ao tomar os respectivos ínfimos e comparar com $CN^{-s}$, resultam $H(N)\ge(c_G/C)^{1/s}N$, $H(N)\ge(c_L/C)^{1/\beta}N^{s/\beta}$ quando $s\le1/p$, e $H(N)\ge N^s/(2C)$. Aqui $s/\beta=1+1/p-s$.

Em $N\ge2$, a Proposição 5.3 dá $e^{H(N)}_{N,p}(f)\le R_{N,H(N)}(f)_p$. A hipótese uniforme de realização implica a de melhor erro, portanto os mesmos pisos seguem. A discussão da potência ótima em `lp:obs:floor-closure` está no regime minimax $N,H\ge2$. A observação `lp:obs:loglog` usa a necessidade em taxas por escala, e a soma diádica da realização começa em $r=1$.

### E4.1 · Suporte, normas e empacotamento

Para $m\ge1$ e $0\le j<m$, a transformação $y=mx-j$ leva $((j/m),(j+1)/m)$ a $(0,1)$. Após a extensão por zero, o suporte da função reescalada é a imagem de $\operatorname{supp}\varphi$ pelo mapa inverso $y\mapsto(j+y)/m$. É compacto e está dentro da célula aberta. Os suportes são dois a dois disjuntos, inclusive para as segundas derivadas, que se anulam fora dos suportes originais.

A substituição dá $\|\varphi(m\cdot-j)\|_p^p=m^{-1}c_\varphi^p$. Com $a=B/C_1$, somar em suportes disjuntos produz $\|f_\theta\|_p^p=a^pm^{-sp-1}|\theta|c_\varphi^p$. As segundas derivadas introduzem o fator $m^2$ e dão $\|f_\theta''\|_p\le a m^{2-s}M_\varphi$. Os coeficientes $\theta_j-\eta_j$ têm valor absoluto $1$ em exatamente $d_H(\theta,\eta)$ células, logo

$$
\|f_\theta-f_\eta\|_p=a c_\varphi m^{-s-1/p}d_H(\theta,\eta)^{1/p}.
$$

Com a fórmula integral da segunda diferença e a cota por $4\|f_\theta\|_p$, o módulo é no máximo $C_2a m^{-s}\min\{1,(mt)^2\}$. Na sequência diádica, os dois lados de $r=\log_2m$ decaem com expoentes $s$ e $2-s$, ambos positivos. Para $q<\infty$, transladar a soma por $\lfloor\log_2m\rfloor$ dá o fator $2^{\theta_*}$ em $K_{s,q}$ via $|k-\delta|\ge|k|-1$. Para $q=\infty$, basta a cota uniforme $C_2a$. Portanto $C_1=c_\varphi+C_2K_{s,q}$ garante $\|f_\theta\|^*\le B$.

Para $k=\lfloor m/4\rfloor$, um conjunto maximal com distância mínima pelo menos $k+1$ cobre o cubo por bolas de Hamming de raio $k$. Se $k=0$, o cubo inteiro serve. Se $k\ge1$, a probabilidade de cada palavra de peso no máximo $k$ em Bernoulli de parâmetro $p_0=k/m\le1/4$ é pelo menos $2^{-mH(p_0)}$. Dessa forma, $V(m,k)\le2^{mH(p_0)}\le2^{mH(1/4)}$, pois $H$ cresce em $[0,1/2]$. A relação $3^9>2^{14}$ dá $H(1/4)=2-\frac34\log_2 3<5/6$. Dividir $2^m$ pelo volume máximo garante ao menos $2^{m/6}$ centros, e $k+1>m/4$ dá separação estrita em Hamming.

**Dependências.** `lp:lem:leaf-budget-floor` aplica apenas a cota de norma a $m=2N\ge4$ e soma erros em células sem nós interiores. `lp:prop:entropy-lower` escolhe $m\ge1$ e usa a fórmula de distância e a cardinalidade. A separação de mais de $2\varepsilon$ neste último resultado segue de $m^s<c_3B/(2C_1\varepsilon)$, suficiente para bolas fechadas com centros arbitrários.

### E4.2 · Comprimento máximo e imagem

Há $2^\ell$ palavras de comprimento $\ell$, inclusive uma para $\ell=0$. A soma de $\ell=0$ a $L$ conta $2^{L+1}-1$ palavras possíveis. Cada saída distinta precisa de pelo menos uma palavra e várias palavras podem levar à mesma saída. Pela hipótese de erro, as bolas fechadas de raio $\varepsilon=C_BN^{-s}$ centradas nas saídas de $D$ cobrem a classe. Logo

$$
\mathcal N(\varepsilon)\le|\operatorname{Im}D|\le 2^{L+1}-1<2^{L+1}.
$$

Na faixa $\varepsilon\le\varepsilon_0B$, a Proposição 8.3 dá $\log_2\mathcal N(\varepsilon)\ge c_5N$. A estimativa $L+1\ge c_5N$ comprova o termo $-1$. O argumento independe da biblioteca de saídas. O código livre de prefixo é uma propriedade da construção de `lp:prop:bits`. No Corolário 8.4, todas as palavras de comprimento até $L$ são admissíveis.

### E4.3 · Domínio do resultado de entropia

O corte $\varepsilon_0B$ foi escolhido para que $X=(c_3B/(2C_1\varepsilon))^{1/s}\ge2$. Assim $m=\lceil X\rceil-1$ obedece a $X/2\le m<X$. A cota inferior de $m$ dá a cardinalidade na ordem requerida. A condição $m<X$ garante separação superior ao diâmetro das bolas fechadas. Para $\varepsilon\ge B$, toda a classe cabe na bola fechada com centro zero por $\|f\|_p\le\|f\|^*\le B$, e a classe contém zero. Portanto $\mathcal N(\varepsilon)=1$ e o logaritmo se anula.

O enunciado da Proposição 8.3 cobre as escalas até $\varepsilon_0B$. Uma verificação separada para $\varepsilon_0B<\varepsilon<B$ confirma que o corte específico não é uma necessidade matemática. As funções constantes $f_\pm\equiv\pm B$ têm norma de Besov $B$ e distância $2B$, portanto $\log_2\mathcal N(\varepsilon)\ge1$. Nesse intervalo, $c_4(B/\varepsilon)^{1/s}<c_4\varepsilon_0^{-1/s}=1/6$. Essa verificação, registrada aqui, justifica a distinção de escopo da observação. O enunciado da proposição conserva o intervalo certificado pela construção. A estimativa superior e a equivalência com a norma por wavelets citada no manuscrito ficam fora desta revisão.

### Preservação dos resultados centrais

Foram comparados, nas duas fontes, os blocos completos de enunciado e prova dos seis resultados com o commit auditado. Todos são idênticos. A mesma comparação foi feita para `lp:prop:entropy-lower`. A conferência de dependências encontrou os seguintes usos.

| Resultado | Dependência relevante examinada |
|---|---|
| `lp:lem:nodal-variable-height` | O quantizador depende dos dados nodais e das condições aritméticas locais. Os domínios de realização e a prova de empacotamento não entram em sua construção. |
| `lp:prop:l1-linear-height` | Usa o quantizador por nó em $B^1_{1,q}$ e $n=2^r\ge2$. O custo de realização é usado posteriormente, já dentro do domínio corrigido. |
| `lp:thm:minimax-nh` | Os três pisos de altura são aplicados no domínio $N,H\ge2$. O piso de folhas usa `lp:lem:packing` com $m=2N$ e a mesma constante $C_1$. |
| `lp:cor:minimax-realization` | O alvo está na bola unitária e a família contínua contém zero. A transferência mantém o fator $5$ em $N\ge2$. |
| `lp:thm:critical-fixed-agenda` | A construção de altura linear e o deslocamento diádico usam $1<p<\infty$ e $n,dn\ge2$. A transferência que sustenta a estimativa por escala é aplicada a elementos de $L^p$. |
| `lp:prop:critical-radius-growth` | A cota superior usa a prova da agenda fixa. A testemunha constante e o orçamento diádico $M\ge2$ usados na cota inferior satisfazem o domínio da realização. |

## D. Equivalência PT/EN/ABNT

Os domínios, quantificadores, fórmulas, constantes e argumentos dos seis trechos foram conferidos entre PT e EN. A comparação automatizada de fórmulas foi ampliada aos cinco blocos com prova modificada. Os rótulos mantêm a mesma ordem nas duas fontes. Os arquivos `.aux` das três edições recompiladas conservam os mesmos 117 rótulos e números encontrados nas compilações correspondentes do commit auditado. A ABNT carrega `conjecturas_lp.tex` por `\input`, de modo que a revisão matemática se aplica por inclusão direta.

## E. Testes e compilação

| Verificação | Resultado |
|---|---|
| `python3 -B -m unittest discover -s testes -v` | 9 testes passaram. As duas regressões novas conferem os domínios E3, $m\ge1$ e a cadeia de cardinalidades da imagem em E4.2. A suíte também verifica rótulos, remissões, citações, fórmulas PT/EN e inclusão da fonte PT na ABNT. |
| `python3 -B mapas/gerar_mapa.py` e `python3 -B mapas/verificar_mapa.py` | Mapa regenerado e conferido. 64 entradas e 263 ocorrências de nomes localizadas em fonte e aceitas em `#check`. As notas documentam o domínio estendido das provas Lean do E3. |
| `lake build` em `lean4/formalizacao` | Sucesso em 8.133 tarefas. |
| `lake build Formalizacao RequestProject Pendencias` | Sucesso em 8.189 tarefas, com avisos de lint e depreciação em código preexistente. |
| `lake env lean /tmp/artigo-besov-e3e4.h3cKhM/AxiomasE3.lean` | Auditoria temporária dos nove resultados Lean ligados a E3. Todos listam apenas `propext`, `Classical.choice` e `Quot.sound`. |
| `latexmk -pdf -recorder -interaction=nonstopmode -halt-on-error -file-line-error` | Compilação das três edições com latexmk 4.88 e pdfTeX 1.40.29. Logs finais sem avisos, referências indefinidas ou caixas excedentes. PT 30 páginas, EN 29, ABNT 32. A edição PT passou de 29 a 30 páginas com a repaginação da revisão. |
| `qpdf --check`, `pypdf` e `pdftoppm` | Os três PDFs passaram na verificação estrutural. Conferidos 805 links internos com destino nomeado e inspecionadas 25 páginas renderizadas, cobrindo os trechos revistos, continuações e a página final da edição PT. |
| `git diff --check` e inspeção do diff integral | Sem erros de espaços. As alterações de fontes e do mapa correspondem aos itens auditados e aos seus domínios de definição. |

Na primeira rodada, a verificação de fórmulas encontrou o conector traduzido dentro da equação de normalização e o LaTeX indicou caixas excedentes na linha com os dois domínios de orçamento. O texto final usa uma implicação matemática comum às edições e declara os domínios no parágrafo que introduz as fórmulas. A inspeção de PDFs usou o Python 3.12 do ambiente empacotado após uma incompatibilidade de versão entre Pillow e o Python do sistema.

O comando abaixo reproduz a compilação a partir da raiz.

```bash
saida=$(mktemp -d)
export SOURCE_DATE_EPOCH=$(date -d '2026-11-21 00:00:00 -03:00' +%s)
export FORCE_SOURCE_DATE=1
latexmk -pdf -recorder -interaction=nonstopmode -halt-on-error -file-line-error \
  -outdir="$saida" conjecturas_lp.tex conjecturas_lp_en.tex conjecturas_lp_abnt.tex
for pdf in "$saida"/*.pdf; do
  qpdf --check "$pdf"
done
```

A compilação LaTeX verifica a edição. A equivalência matemática decorre da revisão das fórmulas e provas. O build Lean verifica as declarações existentes. O empacotamento de Besov e suas consequências E4 foram verificados analiticamente, sem certificação Lean correspondente a esses enunciados.

## F. Diferenças finais

As fontes passaram por intervenções nos seis pontos e em três trechos de apoio que tratam do domínio dos orçamentos independentes, da observação que aplica o piso aritmético e da definição da bola. Os PDFs versionados foram regenerados, e o mapa e as regressões refletem os ajustes. O diff mantém os enunciados e as provas dos seis resultados centrais, os arquivos Lean e a fonte de entrada ABNT. As intervenções se limitam a E3/E4 e às dependências registradas acima.

O escopo da avaliação de entropia é o da cota inferior. A comparação bilateral por wavelets permanece fora do artigo e os resultados E4 permanecem analíticos. Os avisos do build Lean são preexistentes. A verificação da intervenção considera as ocorrências detalhadas no pedido da Etapa 4A e as fontes auditadas.

## G. Parecer de encerramento

| Item | Classificação |
|---|---|
| E3.1 | **Corrigido e verificado** |
| E3.2 | **Corrigido e verificado** |
| E3.3 | **Corrigido e verificado** |
| E4.1 | **Corrigido e verificado** |
| E4.2 | **Corrigido e verificado** |
| E4.3 | **Corrigido e verificado** |

PDFs recompilados. [Português](conjecturas_lp.pdf), [inglês](conjecturas_lp_en.pdf) e [ABNT](conjecturas_lp_abnt.pdf).

Fontes editáveis. [PT](conjecturas_lp.tex), [EN](conjecturas_lp_en.tex) e [entrada ABNT](conjecturas_lp_abnt.tex).
