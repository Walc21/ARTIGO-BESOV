#!/usr/bin/env python3
"""Gera mapas/MAPA_TEX_LEAN.md a partir de mapas/dados/mapa_lp.json.

O JSON é a fonte da correspondência. As linhas do TeX são calculadas a partir dos rótulos
`\\label{...}` em conjecturas_lp.tex e as linhas do Lean a partir das declarações nos arquivos
`.lean`, de modo que o mapa nunca aponta para uma linha velha. A verificação dos nomes pelo
próprio Lean fica em verificar_mapa.py.

Uso:
    python3 mapas/gerar_mapa.py               # escreve mapas/MAPA_TEX_LEAN.md
    python3 mapas/gerar_mapa.py --verificar   # falha se o arquivo estiver desatualizado
"""

from __future__ import annotations

import argparse
import collections
import json
import re
import sys
from pathlib import Path

RAIZ = Path(__file__).resolve().parent.parent
DADOS = RAIZ / "mapas" / "dados" / "mapa_lp.json"
SAIDA = RAIZ / "mapas" / "MAPA_TEX_LEAN.md"
TEX = RAIZ / "conjecturas_lp.tex"

PREFIXOS = r"(?:@\[[^\]]*\]\s*)?(?:(?:protected|private|noncomputable|partial|unsafe)\s+)*"
TIPOS = r"(?:theorem|lemma|def|abbrev|structure|instance|inductive|class)"


def linha_do_rotulo(rotulo: str) -> int:
    alvo = "\\label{" + rotulo + "}"
    linhas = [n for n, t in enumerate(TEX.read_text(encoding="utf-8").split("\n"), 1) if alvo in t]
    if len(linhas) != 1:
        raise ValueError(f"o rótulo {rotulo!r} aparece {len(linhas)} vezes em {TEX}")
    return linhas[0]


def arquivo_absoluto(rel: str) -> Path:
    return (RAIZ / "mapas" / rel).resolve()


def linha_da_declaracao(nome: str, arquivo: str) -> int:
    caminho = arquivo_absoluto(arquivo)
    if not caminho.is_file():
        raise ValueError(f"arquivo inexistente para {nome!r}: {caminho}")
    ultimo = nome.split(".")[-1]
    padrao = re.compile(r"^\s*" + PREFIXOS + TIPOS + r"\s+" + re.escape(ultimo) + r"(?![\w'])")
    achados = [n for n, t in enumerate(caminho.read_text(encoding="utf-8").split("\n"), 1)
               if padrao.match(t)]
    if len(achados) != 1:
        raise ValueError(f"{nome!r}: {len(achados)} declarações em {caminho}")
    return achados[0]


def gerar(dados: dict) -> str:
    saida = dados["cabecalho"].rstrip("\n").split("\n") + ["", "## Correspondências", ""]
    contagem: collections.Counter[str] = collections.Counter()
    for e in dados["entradas"]:
        contagem[e["estado"]] += 1
        saida += [f"### {e['id']} — {e['titulo']}", ""]
        n = linha_do_rotulo(e["rotulo"])
        saida += [f"Texto: [conjecturas_lp.tex:{n}](../conjecturas_lp.tex); rótulo `{e['rotulo']}`.", ""]
        saida += [f"Estado: **{e['estado']}**. {e['nota']}".rstrip(), ""]
        for ref in e["lean"]:
            linha = linha_da_declaracao(ref["nome"], ref["arquivo"])
            saida.append(f"- [`{ref['nome']}`]({ref['arquivo']}) — linha {linha}.{ref['nota']}")
        if e["lean"]:
            saida.append("")
    saida += ["## Resumo", "", "| Estado | Entradas |", "|---|---|"]
    for estado, qtd in contagem.most_common():
        saida.append(f"| {estado} | {qtd} |")
    return "\n".join(saida) + "\n"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--verificar", action="store_true")
    args = ap.parse_args(argv)
    texto = gerar(json.loads(DADOS.read_text(encoding="utf-8")))
    if args.verificar:
        if not SAIDA.is_file() or SAIDA.read_text(encoding="utf-8") != texto:
            print("MAPA_TEX_LEAN.md está desatualizado; execute mapas/gerar_mapa.py", file=sys.stderr)
            return 1
        print("MAPA_TEX_LEAN.md está atualizado.")
        return 0
    SAIDA.write_text(texto, encoding="utf-8")
    print(f"escrito {SAIDA}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
