/-
  PR-25 · `verification_sans_divulgation`
  =======================================

  **Premier appui formel revendiqué du palier PAL-5** — accès limité,
  vérifiabilité conservée.

  D'OÙ IL VIENT, ET POURQUOI IL ARRIVE TARD
  ------------------------------------------
  Le graphe classait PAL-5 comme un palier **sans appui formel**, en
  renvoyant au plan V.3.5 et aux mécanismes de type blockchain. Le bilan
  du 8 septembre a remarqué que l'appui existait depuis le 7, sans avoir
  été revendiqué : le graphe note lui-même que **L2 « soutient PAL-2 et
  PAL-5 »**, et `accord_sur_l_existence_pas_sur_la_valeur` (PR-20 §4) dit
  littéralement ce que PAL-5 demande.

  Ce fichier tire la conséquence, et **elle n'était pas déductible de
  PR-20 seul** : PR-20 montre que deux registres peuvent diverger sur la
  valeur ; PR-25 montre qu'un **observateur privé du registre
  financier** conclut quand même — c'est-à-dire que la divergence n'est
  pas une perte de vérifiabilité.

  L'ÉNONCÉ
  --------
  > **Un tiers qui ne voit que le registre de communalité décide
  > l'existence de la contrepartie, sans aucun accès au registre
  > financier ; et deux registres augmentés qui ne diffèrent que par les
  > valeurs financières lui sont indiscernables.**

  Accès limité d'un côté, vérifiabilité conservée de l'autre : c'est PAL-5.

  CE QUE CE FICHIER NE FAIT PAS, ET IL FAUT LE LIRE AVANT LE RESTE
  ----------------------------------------------------------------
  · Il **ne rend rien confidentiel**. Rien ici ne cache `pFin` : le
    fichier montre qu'il n'est **pas nécessaire**, ce qui est une
    propriété du registre, pas un mécanisme de protection. §4.
  · Il **n'établit aucune véridiction substantielle**. Ce que le tiers
    vérifie est l'**existence de la contrepartie**, jamais la vérité de
    ce qu'elle dit. La réserve du plan V.3.5 — la blockchain établit une
    véridiction *procédurale* (date, intégrité, version), jamais
    *substantielle* — **n'est pas formalisable et reste déclarée**. §4.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.LotL2_PR2_PR14`.

  [D-ED-2, 29/09/2026] `EcritureDuale` renommé `RegistreComptableAugmente` : les
  « écritures duales » de ce fichier sont des registres comptables
  augmentés (N3), non l'écriture duale entre teneurs (N2, PR-35).
-/

import ProfReg.LotL2_PR2_PR14

namespace ProfRegPR25

open ProfRegLot

variable {Vfin Vcom : Type}

/-! ## 1. L'observateur à accès limité

Il ne dispose que du registre de communalité et de sa valeur pleine.
**Le registre financier n'apparaît pas dans son type** — ce n'est pas
une convention de lecture, c'est une contrainte de signature. -/

/-- Ce que lit un tiers qui n'a accès qu'au registre de communalité.
    Sa conclusion : « la contrepartie existe entre `a` et `b` ». -/
def lectureCom (pCom : Actor → Actor → Vcom) (pleinCom : Vcom)
    (a b : Actor) : Prop :=
  pCom a b = pleinCom

/-! ## 2. La vérification est conservée -/

/-- **PR-25 (1).** L'observateur restreint au registre de communalité
    **décide l'existence du lien** : sa lecture équivaut au socle.

    C'est `compatCom` lu du bon côté — et c'est ce qui fait que l'accès
    limité n'est pas une perte d'information sur ce qui compte. -/
theorem la_lecture_com_decide_le_lien (e : RegistreComptableAugmente Vfin Vcom) (a b : Actor) :
    lectureCom e.pCom e.pleinCom a b ↔ e.socle a b = true :=
  e.compatCom a b

/-- **PR-25 (2).** Et sa conclusion **coïncide avec celle d'un
    observateur qui verrait le registre financier**. Aucun des deux ne
    peut contredire l'autre sur l'existence de la contrepartie.

    C'est `registre_augmente_coherent` réutilisé — le théorème n'est pas
    réécrit, il est appliqué à la question de l'accès. -/
theorem les_deux_observateurs_concluent_pareil (e : RegistreComptableAugmente Vfin Vcom)
    (a b : Actor) :
    lectureCom e.pCom e.pleinCom a b ↔ e.pFin a b = e.pleinFin :=
  (registre_augmente_coherent e a b).symm

/-- **Et la symétrie R1 survit à l'accès limité.** Le tiers qui ne voit
    que la communalité peut aussi conclure que si la contrepartie existe
    de `a` vers `b`, elle existe de `b` vers `a` — pourvu que le socle
    satisfasse R1. `registre_augmente_preserve_R1` appliqué. -/
theorem la_symetrie_reste_lisible_en_acces_limite
    (e : RegistreComptableAugmente Vfin Vcom) (h_R1 : R1_actoriel e.socle) :
    ∀ a b, lectureCom e.pCom e.pleinCom a b → lectureCom e.pCom e.pleinCom b a :=
  (registre_augmente_preserve_R1 e h_R1).2

/-! ## 3. Et la valeur financière n'est pas divulguée

Deux registres augmentés que l'observateur restreint ne peut pas
distinguer, et dont les valeurs financières diffèrent. -/

/-- Deux registres augmentés sur le même socle vide, de même registre de
    communalité, dont les registres financiers divergent hors du point
    plein. Elles satisfont l'une et l'autre L2. -/
-- [B-3, 28/09/2026] Témoins refaits : le socle était VIDE, et les registres ne
-- divergeaient que là où il n'y a aucun lien (forme 6). Les nouveaux témoins
-- portent un lien (le socle est complet) et divergent SUR ce lien : la valeur
-- pleine du registre financier est 1 dans l'un, 7 dans l'autre, et la lecture de
-- communalité est la même. Réserve CONV-10 : dans L2, `plein` signifie que le
-- registre reconnaît le lien, non qu'il le valorise ; ce qui n'est pas divulgué
-- est la **manière dont le registre financier inscrit le lien**, non un montant.
def temoinA : RegistreComptableAugmente Nat Bool :=
  { socle := fun _ _ => true
  , pFin := fun _ _ => 1
  , pCom := fun _ _ => true
  , pleinFin := 1
  , pleinCom := true
  , compatFin := fun _ _ => ⟨fun _ => rfl, fun _ => rfl⟩
  , compatCom := fun _ _ => ⟨fun _ => rfl, fun _ => rfl⟩ }

def temoinB : RegistreComptableAugmente Nat Bool :=
  { socle := fun _ _ => true
  , pFin := fun _ _ => 7
  , pCom := fun _ _ => true
  , pleinFin := 7
  , pleinCom := true
  , compatFin := fun _ _ => ⟨fun _ => rfl, fun _ => rfl⟩
  , compatCom := fun _ _ => ⟨fun _ => rfl, fun _ => rfl⟩ }

/-- **PR-25 (3) — l'inscription financière du lien n'est pas divulguée.** Il existe deux registres augmentés
    **cohérentes l'une et l'autre**, de **même registre de communalité**
    et de **même valeur pleine**, dont les **registres financiers
    diffèrent** — et que l'observateur restreint lit donc à
    l'identique.

    **Accès limité, vérifiabilité conservée** : la lecture est la même,
    l'inscription financière du lien ne l'est pas — au sens de CONV-10 : la manière
    dont le registre financier inscrit le lien, non un montant. C'est l'appui de PAL-5. -/
-- [B-3, 28/09/2026] Sur les nouveaux témoins, la divergence porte sur un lien existant (socle complet).
-- [B-3, 28/09/2026 — RENOMMÉ, ex-`la_valeur_financiere_n_est_pas_divulguee`] le nom dit ce que l'énoncé établit (réserve CONV-10).
theorem l_inscription_financiere_du_lien_n_est_pas_divulguee :
    (∀ a b, lectureCom temoinA.pCom temoinA.pleinCom a b
            ↔ lectureCom temoinB.pCom temoinB.pleinCom a b)
  ∧ (∃ a b, temoinA.pFin a b ≠ temoinB.pFin a b) := by
  constructor
  · intro a b; exact Iff.rfl
  · exact ⟨"A", "B", by decide⟩

/-- **Et les deux témoins sont bien des registres augmentés cohérents** —
    sans quoi le théorème précédent porterait sur des objets mal
    formés. On le montre en réutilisant `registre_augmente_coherent`. -/
theorem les_deux_temoins_sont_coherents :
    (∀ a b, temoinA.pFin a b = temoinA.pleinFin
            ↔ temoinA.pCom a b = temoinA.pleinCom)
  ∧ (∀ a b, temoinB.pFin a b = temoinB.pleinFin
            ↔ temoinB.pCom a b = temoinB.pleinCom) :=
  ⟨registre_augmente_coherent temoinA, registre_augmente_coherent temoinB⟩

/-! ## 4. Gardes — et les deux premières bornent la portée du palier -/

/-- **PR-25 n'établit aucune confidentialité.** Rien ici ne cache
    `pFin` : le fichier montre qu'il n'est **pas nécessaire** à la
    vérification. C'est une propriété du registre, pas un mécanisme de
    protection — et un dispositif qui divulguerait `pFin` ne
    contredirait aucun théorème de ce fichier.

    On l'inscrit en exhibant un registre augmenté dont le registre
    financier est parfaitement lisible et qui satisfait tout ce qui
    précède. -/
theorem PR25_n_etablit_aucune_confidentialite :
    ∀ a b, temoinA.pFin a b = 1 := fun _ _ => rfl

/-- **PR-25 n'établit aucune véridiction substantielle.** Ce que le
    tiers décide est l'**existence** de la contrepartie, jamais la
    vérité de ce qu'elle porte : les deux témoins s'accordent sur
    l'existence tout en portant des valeurs différentes.

    C'est la réserve du plan V.3.5 — véridiction **procédurale** (date,
    intégrité, version), **jamais substantielle** — et elle **n'est pas
    formalisable** : elle se déclare. Ce théorème en donne la
    contrepartie inspectable, non la preuve. -/
theorem PR25_ne_verifie_que_l_existence :
    (∀ a b, lectureCom temoinA.pCom temoinA.pleinCom a b
            ↔ lectureCom temoinB.pCom temoinB.pleinCom a b)
  ∧ temoinA.pFin "A" "B" ≠ temoinB.pFin "A" "B" :=
  ⟨l_inscription_financiere_du_lien_n_est_pas_divulguee.1, by decide⟩

/-- **PR-25 n'exige aucune harmonisation des évaluations.** C'est la
    garde de PR-20 (`accord_sur_l_existence_pas_sur_la_valeur`), portée
    ici au palier : exiger que les deux registres disent la même chose
    supprimerait précisément ce que PAL-5 obtient. -/
theorem PR25_n_exige_aucune_harmonisation :
    temoinA.socle = temoinB.socle ∧ temoinA.pFin ≠ temoinB.pFin := by
  refine ⟨rfl, ?_⟩
  intro h
  have hab := congrFun (congrFun h "A") "B"
  exact absurd hab (by decide)

/-! [C-14 — RETIRÉ LE 28/09/2026, décision du porteur] `PR25_ne_conclut_pas_P5`
    était le sens → de `la_lecture_com_decide_le_lien` sous un nom de délimitation :
    patron exact de `PR24_ne_conclut_pas_P1` (A-8). La délimitation reste en prose :
    PR-25 fournit le maillon formel — la vérification survit à l'accès limité —
    dans un palier PAL-5 qui reste **procédural** ; les mécanismes concrets et la
    réserve de véridiction sont hors du champ de la preuve. Garde de non-régression déclarée : ne pas réintroduire ce théorème sous un autre nom. -/

/-- **Témoin discriminant** (R-7, 28/09/2026) de `la_lecture_com_decide_le_lien` :
    la lecture de communalité est vraie sur `temoinA`, et fausse sur un registre
    augmenté dont le socle est vide. -/
theorem la_lecture_com_temoin_discriminant :
    lectureCom temoinA.pCom temoinA.pleinCom "A" "B"
    ∧ ∃ (e : RegistreComptableAugmente Bool Bool) (a b : Actor), ¬ lectureCom e.pCom e.pleinCom a b :=
  ⟨rfl, ⟨{ socle := fun _ _ => false, pFin := fun _ _ => false, pCom := fun _ _ => false, pleinFin := true, pleinCom := true, compatFin := fun _ _ => Iff.rfl, compatCom := fun _ _ => Iff.rfl }, "A", "B", fun h => Bool.noConfusion h⟩⟩

end ProfRegPR25
