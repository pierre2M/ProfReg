/-
  PR-22 · `regime_declare_par_un_porteur`
  =======================================

  **Exécution de la décision 1 de la tâche 12ter** (8 septembre 2026,
  décision de porteur) : le composite `P + C` de la sous-couche
  C-MOUVEMENT-TYPE.T **remonte en couche R**.

  LA RAISON, ET ELLE N'EST PAS CELLE QUE J'AVAIS PROPOSÉE
  -------------------------------------------------------
  J'avais posé l'alternative ainsi : ou bien la double nature du sol
  agricole est **ontologique** et elle reste en couche T, ou bien elle
  est **conventionnelle** et elle appartient à R — en ajoutant que le
  MRC a une raison de préférer la première.

  **L'alternative était fausse.** Le porteur la corrige :

    « C'est au collectif de décider de la nature ontologique, voire
      des natureS ontologiqueS attachées à une chose qui fait l'objet
      d'un attachement collectif. »

  Le régime n'est donc pas le contraire de l'ontologique : **c'est le
  lieu où la décision du collectif sur la nature de la chose
  s'inscrit**. Un sol peut être un foncier de valeur marchande sous
  certaines conditions et un substrat du vivant sous d'autres, et c'est
  le collectif attaché à la chose qui pose ces conditions.

  Remonter `P + C` en couche R ne déclasse donc pas le sol agricole :
  **cela nomme qui décide.**

  CE QUE LA DÉCISION EXIGE, ET QUE LA COUCHE R N'A PAS
  ----------------------------------------------------
  La couche R porte sept champs — `sigle_mouvement_ref`,
  `regime_comptable`, `denomination_regime`, `compte_imputation`,
  `conditions_reconnaissance`, `exemple_chiffre`, `traduction_uri`.
  [A-7 — ÉTAT AU 8/09. Depuis le 19/09 : `traduction_uri` devient une clé composite
  (`sigle_mouvement` × `regime_comptable`), `traduction_uri_ref` facultatif
  (NT-ARCH §8.5, entrée C3).]
  **Aucun porteur**, et `regime_comptable` est une **énumération close** :
  IFRS / PCG / US_GAAP / CARE / GESTION / IIRC / LIFTS / ACTION.
  [A-7 — ÉTAT AU 8/09. Depuis : registre OUVERT des régimes déclarés, avec porteur,
  date et condition de réfutation (NT-ARCH §8.4ter, 20/09) ; LIFTS et ACTION retirés,
  US_GAAP et IIRC en CANDIDAT_NON_INSTANCIABLE (arbitrage 4, 26/09). La décision que
  ce fichier démontre nécessaire — ouvrir l'énumération — a donc été prise.
  Aucun théorème de ce fichier ne dépend de ces valeurs.]

  Deux conséquences, et ce fichier les démontre plutôt que de les
  plaider :
    (1) un régime déclaré par un collectif exige un PORTEUR — patron de
        PR-18, où le porteur du seuil est exhibé avec sa population ;
    (2) l'énumération close **exclut nécessairement** un collectif dès
        que la population des collectifs n'est pas énumérable — c'est
        `liste_close_exclut_toujours` (PR-16), appliqué au régime et non
        plus à la réfutation.

  Porteur : Pierre Musseau. Décision et écriture du 8 septembre 2026.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR16_RefutationTiers`.
-/

import ProfReg.PR16_RefutationTiers

namespace ProfRegPR22

open ProfRegPR16

/-! ## 1. Un régime de qualification, et qui le déclare

Un **régime** dit sous quelles conditions une chose compte comme quoi.
Les régimes comptables établis — IFRS, PCG, CARE — en sont des cas ;
les sept critères de qualité arrêtés par un Comité Citoyen en sont un
autre, qu'aucune instance de normalisation n'a émis. -/

/-- Un régime de qualification, avec **son porteur**. C'est le champ que
    la couche R n'a pas. -/
structure RegimeQualification (A : Type) where
  nom : String
  /-- Qui a déclaré ce régime. Patron de `porteurDeLaDeclaration`
      (PR-18) : le porteur est exhibé par construction du type. -/
  porteur : A
  /-- Sous quelles conditions la chose compte comme ce que le régime
      dit qu'elle est. -/
  conditions : String

/-- La **qualification** d'une chose : la nature qui lui est attribuée
    dans un régime donné. -/
structure Qualification (A : Type) where
  chose : String
  regime : RegimeQualification A
  nature : String

/-! ## 2. Une même chose porte plusieurs natures — et c'est le cas `P + C`

C'est ce que le composite disait, et que la couche R dit mieux : deux
qualifications de la même chose, chacune dans son régime, chacune avec
son porteur. -/

def collectifRoubaix : String := "comite-citoyen"
def normalisateurIFRS : String := "IASB"

/-- Le sol comme foncier de valeur marchande — régime IFRS/PCG. -/
def solCommeFoncier : Qualification String :=
  { chose := "sol agricole"
  , regime := { nom := "IFRS/PCG"
              , porteur := normalisateurIFRS
              , conditions := "actif contrôlé, avantages économiques futurs" }
  , nature := "P — patrimoine" }

/-- Le même sol comme substrat du vivant — régime déclaré par le
    collectif attaché à la chose. -/
def solCommeSubstrat : Qualification String :=
  { chose := "sol agricole"
  , regime := { nom := "régime déclaré par le collectif"
              , porteur := collectifRoubaix
              , conditions := "fertilité maintenue, vivant du sol préservé" }
  , nature := "C — créance écologique" }

/-- **Une même chose, deux natures, deux régimes, deux porteurs.**
    C'est le contenu de l'ancien composite `P + C`, désormais placé là
    où il dit qui décide. -/
theorem une_chose_deux_natures :
    solCommeFoncier.chose = solCommeSubstrat.chose
  ∧ solCommeFoncier.nature ≠ solCommeSubstrat.nature
  ∧ solCommeFoncier.regime.porteur ≠ solCommeSubstrat.regime.porteur := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-! [C-6 — RETIRÉ LE 28/09/2026, décision du porteur] `la_qualification_exhibe_son_porteur`
    énonçait `∃ p, q.regime.porteur = p` : vrai de tout champ (forme 1). Le porteur
    est lisible sur la qualification parce qu'il en est un **champ** — c'est la
    définition de `Qualification`, non un théorème. Les citations de NT-ARCH et de
    NT-G7 renvoient désormais à la définition. Garde de non-régression déclarée : ne pas réintroduire ce théorème sous un autre nom. -/

/-! ## 3. La conséquence dure : une énumération close de régimes exclut

`regime_comptable` ~~est aujourd'hui~~ **était au 8 septembre** une énumération close de huit
valeurs [A-7 : ouverte depuis le 20/09, NT-ARCH §8.4ter]. Si les régimes peuvent être déclarés par des collectifs, et
si la population des collectifs n'est pas énumérable, **toute liste
close en exclut un**.

Ce n'est pas une analogie : c'est `liste_close_exclut_toujours`
(PR-16), écrit pour les réfutants, appliqué ici aux porteurs de régime.
Le théorème est réutilisé, non réécrit. -/

/-- On réutilise la structure de PR-16 : `refutantsAdmis` y code une
    liste close ou l'ouverture. Ici la même forme code **les porteurs
    de régime admis**. -/
abbrev RegimesAdmis (A : Type) := ConditionRefutation A

/-- **L'énumération close exclut.** Dès que la population des porteurs
    de régime n'est pas énumérable, une liste close en laisse un
    dehors. Application directe de PR-16. -/
-- [C-12 — 28/09/2026] Instance déclarée de `liste_close_exclut_toujours` (PR-16),
-- spécialisée aux porteurs de régime. Aucun contenu propre au-delà de PR-16.
theorem enumeration_close_exclut_un_collectif {A : Type}
    (h_ne : NonEnumerable A) (r : RegimesAdmis A) (l : List A)
    (h_clos : r.refutantsAdmis = some l) :
    ∃ a : A, ¬ ExercablePar r a :=
  liste_close_exclut_toujours h_ne r l h_clos

/-- **Et seule l'ouverture n'exclut personne.** Même source, même
    théorème : `ouverture_n_exclut_personne`. -/
-- [C-12 — 28/09/2026] Instance déclarée de `ouverture_n_exclut_personne` (PR-16).
theorem seule_l_ouverture_admet_tout_collectif {A : Type}
    (r : RegimesAdmis A) (h : r.refutantsAdmis = none) :
    ∀ a : A, ExercablePar r a :=
  ouverture_n_exclut_personne r h

-- **Non-énumérabilité des collectifs — hypothèse de modélisation, déclarée.** Les
-- collectifs sont indexés par `Nat` ; que leur population ne soit épuisée par aucune
-- liste finie est la *portée visée*, non établie par un énoncé. L'instance sur `Nat`
-- est `ProfRegPR16.nat_non_enumerable`, comme pour les tiers de PR-16.
-- [12/10/2026 — RETIRÉ, doublon d'énoncé : `les_collectifs_indexes_par_Nat_ne_sont_pas_enumerables`
--  (`NonEnumerable Nat`, preuve `nat_non_enumerable`) ; son seul usage, ci-dessous, pointe
--  désormais sur `nat_non_enumerable` ; nommé par aucun fichier du set MRC v5.7.]

/-- **Une liste close de collectifs indexés par `Nat` exclut quelqu'un**
    (instance de `liste_close_exclut_toujours`). *Portée visée — déclarée, non établie par l'énoncé :*  Si `regime_comptable` reste une énumération
    close, il exclut un porteur de régime possible ; s'il s'ouvre, il
    n'en exclut aucun. **La décision 1 rend donc l'ouverture de ce
    champ nécessaire**, et ce n'est pas un confort de modélisation. -/
-- [B-10, 28/09/2026 — RENOMMÉ, ex-`la_decision_1_exige_l_ouverture`] Instance sur `Nat` de `liste_close_exclut_toujours` : une liste close exclut quelqu'un. « Exige » n'est pas démontré ; c'est la lecture qu'en fait la décision 1.
theorem une_liste_close_de_collectifs_Nat_exclut_quelqu_un (r : RegimesAdmis Nat) (l : List Nat)
    (h_clos : r.refutantsAdmis = some l) :
    ∃ a : Nat, ¬ ExercablePar r a :=
  enumeration_close_exclut_un_collectif nat_non_enumerable r l h_clos

/-! ## 4. Gardes -/

/-- **PR-22 ne dit pas que tous les régimes se valent.** Il dit qu'aucun
    ne peut être exclu *par la forme du champ*. Deux qualifications de
    la même chose restent distinctes, et rien ici ne les départage. -/
theorem PR22_ne_departage_pas_les_regimes :
    solCommeFoncier.nature ≠ solCommeSubstrat.nature
  ∧ solCommeFoncier.regime.nom ≠ solCommeSubstrat.regime.nom := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **PR-22 ne supprime pas les régimes établis.** IFRS reste un régime
    parmi les régimes, avec son porteur nommé — l'ouverture du champ ne
    déclasse rien, elle cesse d'exclure. -/
theorem PR22_ne_supprime_pas_les_regimes_etablis :
    solCommeFoncier.regime.porteur = normalisateurIFRS := rfl

/-- **PR-22 ne dit rien du miroir.** La question du miroir des
    composites était l'objet de 12ter ; une fois `P + C` remonté en
    couche R, elle ne se pose plus pour ce cas — le miroir se prend
    **régime par régime**, et chaque qualification a le sien. Ce
    fichier ne le calcule pas : il constate que les deux
    qualifications sont séparées. -/
theorem PR22_ne_calcule_aucun_miroir :
    solCommeFoncier.regime ≠ solCommeSubstrat.regime := by
  intro h
  have : solCommeFoncier.regime.porteur = solCommeSubstrat.regime.porteur :=
    congrArg RegimeQualification.porteur h
  exact absurd this (by decide)

end ProfRegPR22
