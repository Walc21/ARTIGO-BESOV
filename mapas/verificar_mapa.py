#!/usr/bin/env python3
"""Confere o mapa TeX → Lean.

1. Cada rótulo existe, uma única vez, em conjecturas_lp.tex.
2. Cada nome Lean é declarado, uma única vez, no arquivo indicado.
3. O próprio Lean aceita cada nome (`#check @nome`), em um arquivo temporário.
4. mapas/MAPA_TEX_LEAN.md está igual ao gerado.

Não verifica a fidelidade semântica dos enunciados.

Uso (a partir da raiz do projeto):  python3 mapas/verificar_mapa.py
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gerar_mapa as g  # noqa: E402

PROJETO_LEAN = g.RAIZ / "lean4" / "formalizacao"


def main() -> int:
    dados = json.loads(g.DADOS.read_text(encoding="utf-8"))
    erros: list[str] = []
    nomes: list[str] = []
    for e in dados["entradas"]:
        try:
            g.linha_do_rotulo(e["rotulo"])
        except ValueError as ex:
            erros.append(str(ex))
        for ref in e["lean"]:
            try:
                g.linha_da_declaracao(ref["nome"], ref["arquivo"])
            except ValueError as ex:
                erros.append(str(ex))
            nomes.append(ref["nome"])
    if erros:
        print("\n".join(erros), file=sys.stderr)
        return 1
    print(f"{len(dados['entradas'])} entradas; {len(nomes)} nomes Lean localizados.")
    # (3) #check pelo próprio Lean
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, encoding="utf-8") as f:
        f.write("import Formalizacao\nimport Pendencias.Agenda\nimport Pendencias.Direta\n")
        f.write("import RequestProject.JointBudget\nimport RequestProject.Trees\n")
        for n in dict.fromkeys(nomes):
            f.write(f"#check @{n}\n")
        caminho = f.name
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan" / "bin") + os.pathsep + env.get("PATH", "")
    res = subprocess.run(["lake", "env", "lean", caminho], cwd=PROJETO_LEAN, env=env,
                         capture_output=True, text=True)
    os.unlink(caminho)
    erro = re.search(r"\.lean:\d+:\d+: error", res.stdout + res.stderr)
    if res.returncode != 0 or erro:
        print(res.stdout[-3000:], res.stderr[-3000:], file=sys.stderr)
        print("O Lean rejeitou algum nome.", file=sys.stderr)
        return 1
    print("O Lean aceitou todos os nomes (#check).")
    # (4) mapa atualizado
    return g.main(["--verificar"])


if __name__ == "__main__":
    raise SystemExit(main())
