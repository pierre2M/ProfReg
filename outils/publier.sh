#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-only
# Publie sur GitHub le SEUL état courant du dépôt : un commit unique, sans parent,
# qui porte l'arbre de HEAD. L'historique complet reste local (branche main locale).
# Toute autre branche et tout tag sont retirés du dépôt public.
# Usage : outils/publier.sh ["message"]      (depuis la branche main, arbre propre)
set -euo pipefail
REMOTE=${REMOTE:-origin}
cd "$(git rev-parse --show-toplevel)"
[ -z "$(git status --porcelain)" ] || { echo "Arbre de travail non propre : commitez d'abord." >&2; exit 1; }
[ "$(git rev-parse --abbrev-ref HEAD)" = main ] || { echo "Publier depuis la branche main." >&2; exit 1; }
ARBRE=$(git rev-parse 'HEAD^{tree}')
LOCAL=$(git rev-parse --short HEAD)
MSG=${1:-"État publié le $(date +%F)"}
PUB=$(git commit-tree "$ARBRE" -m "$MSG" -m "Arbre $ARBRE (commit local $LOCAL). Seul l'état courant est publié ; l'historique est conservé localement.")
MRC_PUBLIER=1 git push --force "$REMOTE" "$PUB:refs/heads/main"
git ls-remote --heads --tags "$REMOTE" | awk '{print $2}' | grep -v '\^{}$' | grep -vx 'refs/heads/main' |
while read -r REF; do MRC_PUBLIER=1 git push "$REMOTE" ":$REF"; done
git update-ref refs/publie/main "$PUB"
echo "Publié : $PUB — arbre $ARBRE"
