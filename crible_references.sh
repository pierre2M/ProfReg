#!/bin/bash
# crible_references.sh — étape 6, crible C1 du 8 septembre 2026.
# Vérifie que tout identifiant de théorème cité dans les documents existe
# dans les sources Lean. Aurait détecté l'affaire `VJE_commutatif` en une
# seconde ; elle avait été trouvée par hasard.
#
# Usage :  ./crible_references.sh /chemin/vers/dossier/MRC
#
# CE QU'IL NE FAIT PAS, et il faut le lire avant d'agir sur sa sortie :
#  - il produit des FAUX POSITIFS : `def`, noms de fichiers, étiquettes de
#    registre, tout ce qui ressemble à un identifiant sans en être un
#    (`R1_actoriel` est un def, `PR3_AttributionSeuil` un fichier) ;
#  - il ne voit que les identifiants entre accents graves ;
#  - il ne vérifie PAS que l'énoncé cité dit ce que le document lui fait
#    dire. C'est la limite qui a laissé passer F8 : le nom existait, à une
#    lettre près, et le théorème disait autre chose.
#  - les ARCHIVES datées citent légitimement des théorèmes retirés
#    (`VJE_commutatif`, `V10c_*`) : leur présence en sortie est normale.
set -u
DOCS="${1:-$HOME/Documents/Claude/Projects/MRC}"
LEAN="$(cd "$(dirname "$0")" && pwd)"

grep -rhoE "^(theorem|lemma) [A-Za-z_0-9']+" "$LEAN"/ProfReg/*.lean \
  | awk '{print $2}' | sort -u > /tmp/_noms_reels.txt

grep -rhoE '`[A-Za-z][A-Za-z0-9_]*_[A-Za-z0-9_]*`' \
  "$DOCS"/MRC_v5.6/*.md "$DOCS"/ProfReg/*.md "$DOCS"/*.md 2>/dev/null \
  | tr -d '`' | sort -u > /tmp/_cites.txt

echo "== Déclarations dans les sources : $(wc -l < /tmp/_noms_reels.txt)"
echo "== Identifiants cités dans les documents : $(wc -l < /tmp/_cites.txt)"
echo
echo "== Cités et introuvables, filtrés sur les préfixes de théorèmes =="
comm -13 /tmp/_noms_reels.txt /tmp/_cites.txt \
  | grep -E '^(PR|V[0-9]|VJE|CB|B1|R1|CONV)[A-Za-z0-9_]*_' 
echo
echo "== Déclarés mais absents de Audit.lean (hors périmètre du décompte) =="
grep -oE "^#print axioms [A-Za-z_0-9'.]+" "$LEAN"/Audit.lean \
  | sed 's/.* //' | sed 's/.*\.//' | sort -u > /tmp/_noms_audit.txt
comm -23 /tmp/_noms_reels.txt /tmp/_noms_audit.txt
