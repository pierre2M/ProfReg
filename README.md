# ProfReg

Programme de preuve Lean 4 du **Modèle de Registres de Communalité (MRC), version 5.7**.

ProfReg formalise les conditions de bonne formation que le MRC déclare pour ses inscriptions. Il atteste des propriétés **formelles** ; il ne confère à aucune écriture un statut normatif, ne transforme aucune convention ni règle de second ordre en théorème, et ne décide d'aucune question collective. Le texte de référence est le set MRC v5.7 (`MRC_v5.7_NT-ARCH_Architecture_Couches0-3.md`, `MRC_v5.7_ProfReg_Consolide.md`).

## État de référence (7 octobre 2026)

| | |
| --- | --- |
| Théorèmes audités | **604** (584 d'architecture, 20 de texte) |
| `sorryAx` | **0** |
| Théorèmes dépendant de `Classical.choice` | **10** — exactement ceux dont un type est construit sur les réels |
| Déclarations `axiom` | **0** |
| Build | `lake build` : 1 981 jobs, sans erreur |
| Journal | `audit/audit_2026-10-07_D7.log` |
| Identification | l'**arbre git** du commit publié (`git rev-parse HEAD^{tree}`), identique à celui de l'état local correspondant |

## Environnement épinglé

- Chaîne : `leanprover/lean4:v4.31.0-rc1` (`lean-toolchain`)
- Mathlib : révision `1a59aa5b8603fd850ee2dc6ef9e35a44fe351599` (`lakefile.lean`, `lake-manifest.json`)

## Rejouer

```bash
lake exe cache get
lake build
lake env lean Audit.lean > audit_rejoue.log
grep -c "^'" audit_rejoue.log          # attendu : 604
grep -c sorryAx audit_rejoue.log       # attendu : 0
grep -c Classical.choice audit_rejoue.log  # attendu : 10
lake env lean R7_Controle.lean         # silence attendu (contrôle de la table R-7)
```

**Critère de décompte.** Est compté tout `theorem` ou `lemma` atteignable depuis `ProfReg.lean` et audité par une ligne `#print axioms` dans `Audit.lean`. Un fichier non importé par `ProfReg.lean` n'est pas prouvé.

## Organisation

- `ProfReg.lean` — racine : liste des modules compilés.
- `ProfReg/` — 73 modules (socle catégoriel, vérifications de grammaire, programme PR-1 à PR-59, sonde).
- `Audit.lean` — audit d'axiomes, une ligne par théorème.
- `R7_Controle.lean` — contrôle mécanique de la table des lectures de fonctions (règle R-7) ; ne contient que des `example`, hors décompte.

## Publication

Ce dépôt public ne porte que **l'état courant**, en un seul commit sans historique. Les versions antérieures sont conservées par le porteur, hors ligne. Publication : `outils/publier.sh` ; garde locale contre un push direct : `outils/pre-push`.

## Licence

Copyright (C) 2026 Pierre Musseau-Milesi.

Ce programme est un logiciel libre : vous pouvez le redistribuer et/ou le modifier selon les termes de la **GNU Affero General Public License, version 3** (`SPDX-License-Identifier: AGPL-3.0-only`), telle que publiée par la Free Software Foundation. Il est distribué dans l'espoir qu'il sera utile, mais **sans aucune garantie**. Texte complet : `LICENSE`.
