#!/usr/bin/env bash
# Reproduce the Lean check of the answers to FKS Problem 1 (formal-conjectures pull request 6681).
# Usage: bash check.sh /path/to/formal-conjectures
#   Tested with a formal-conjectures checkout at commit ab0addc45f699bdd0b7cc58efa5140a72f101a9e
#   (Lean v4.33.1, the checkout's lean-toolchain). Run `lake exe cache get` in the checkout first.
#   The statement file of pull request 6681 (head 339f18ba, file
#   FormalConjectures/Arxiv/1802.03092/EmbeddingGraphs.lean) is included here byte-identically as
#   DMSolutions/FKS_Problem1/EmbeddingGraphs.lean and compiled with the repository's leanOptions.
set -euo pipefail
FC="$(cd "$1" && pwd)"
HERE="$(cd "$(dirname "$0")" && pwd)"
D=DMSolutions/FKS_Problem1
mkdir -p "$FC/$D"
cp "$HERE"/$D/*.lean "$FC/$D/"
cd "$FC"
O=.lake/build/lib/lean
mkdir -p "$O/$D"
echo "== formal-conjectures commit: $(git rev-parse HEAD)"
echo "== statement file git blob: $(git hash-object $D/EmbeddingGraphs.lean)  (pull request 6681: b70e39b9...)"
# The repository's own leanOptions for the FormalConjectures library (lakefile.toml).
PKG="-Dpp.unicode.fun=true -DautoImplicit=false -DrelaxedAutoImplicit=false"
PKG="$PKG -Dweak.linter.style.copyright.formalConjectures=true -Dweak.linter.style.namespace=true"
PKG="$PKG -Dweak.linter.style.stubs=true -Dweak.linter.style.openClassical=true"
FCO="-Dwarn.sorry=false -Dweak.linter.style.ams_attribute=true -Dweak.linter.style.category_attribute=true"
FCO="$FCO -Dweak.linter.style.category_answer=true -Dweak.linter.style.conditional_formal_proof=true"
FCO="$FCO -Dweak.linter.style.moduleDocstring=true -Dweak.linter.style.latex_docstring=true"
FCO="$FCO -Dweak.linter.style.imports=true -Dweak.google.answer=always_true"
echo "== 1. Core.lean (Mathlib only)"
lake env lean -o "$O/$D/Core.olean" $D/Core.lean
echo "== 2. EmbeddingGraphs.lean (unmodified statement file, repository options)"
lake env lean $PKG $FCO -o "$O/$D/EmbeddingGraphs.olean" $D/EmbeddingGraphs.lean
echo "== 3. Solution.lean (imports the statement file and Core)"
lake env lean -o "$O/$D/Solution.olean" $D/Solution.lean
echo "== 4. CheckAnswer.lean (answer(False) = False; definitions agree; statements printed)"
lake env lean $D/CheckAnswer.lean
echo "== 5. forbidden keywords (sorry/admit/native_decide/axiom) outside the statement file:"
grep -nE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' $D/Core.lean $D/Solution.lean $D/CheckAnswer.lean || echo "none"
echo "== done"
