-- VJEVerification.lean
-- Commutativité J↔E : couplage G-JUSTICE ↔ G-EVOLUTIVITE (AM-G7-04)
-- NT-G7 v3 §4.2 + §10 — régime vérifiabilité-cohérence
-- DÉCOUPLAGE PARTIEL levé en procédural — commutativité formelle à établir ici

-- [D-14, 27/09/2026] `import Mathlib.Tactic` retiré : superflu — le fichier compile
-- et s'audite à l'identique sans lui (vérifié les 26 et 27/09).
import ProfReg.V3Verification   -- RegimeObligation, PhaseEnquete
import ProfReg.V4Verification   -- StatutDette, NiveauRIA

open ProfReg

namespace VJE

/-- Types des injustices épistémiques (NT-G7 §3.1, AM-G7-02+03)
    Source : Fricker 2007, Dotson 2012, Daukas 2020 -/
inductive TypeInjustice where
  | testimoniale
  | hermeneutique
  | contributoire
  | absente
  deriving DecidableEq

/-- Portée de l'injustice (AM-G7-03)
    Source : Fricker 2007 ch.2 -/
inductive PorteeInjustice where
  | systematique
  | locale
  deriving DecidableEq

/-- Persistance (AM-G7-01, Daukas 2020 p.330) -/
inductive PersistanceInjustice where
  | episodique
  | structurelle
  deriving DecidableEq

/-- État G-JUSTICE : niveauinjusticepistmique structuré -/
structure EtatJustice where
  typeInj       : TypeInjustice
  portee        : PorteeInjustice
  persistance   : PersistanceInjustice
  -- prconditionhermneutiquesatisfaite
  precondSatisfaite : Bool
  -- rsistancecognitivervisionBLOQUANTE
  resistanceBloquante : Bool

/-- État G-EVOLUTIVITE : signal méta-lucidité
    Source : Medina 2013 pp.110-113, via Daukas 2020 p.332 -/
structure EtatEvolutivite where
  -- metaluciditerequise (AM-G7-04 sens JE)
  metaluciditeRequise : Bool
  -- sourceresistancecognitive DID (AM-G7-04)
  sourceResistanceDID : Option String
  -- REVISIONPROXIMATE_ULTIMATE_EFFECTUEE (sens EJ)
  revisionEffectuee : Bool

/-- SENS JE : G-JUSTICE → G-EVOLUTIVITE
    Condition : typeHERMENEUTIQUE ET resistanceBloquante
    Action : metaluciditeRequise := true, sourceResistanceDID obligatoire
    Source : AM-G7-04, NT-G7 §4.2 -/
def appliquerSensJE (j : EtatJustice) (did : String) : EtatEvolutivite :=
  { metaluciditeRequise  :=
      j.typeInj == TypeInjustice.hermeneutique && j.resistanceBloquante
    sourceResistanceDID  :=
      if j.typeInj == TypeInjustice.hermeneutique && j.resistanceBloquante
      then some did
      else none
    revisionEffectuee    := false }

/-- SENS EJ : G-EVOLUTIVITE → G-JUSTICE
    Condition : revisionEffectuee = true
    Action : mise à jour precondSatisfaite selon typeinjusticehermeneutique
    Source : AM-G7-04, NT-G7 §4.2 -/
def appliquerSensEJ (e : EtatEvolutivite) (j : EtatJustice) : EtatJustice :=
  if e.revisionEffectuee
  then { j with precondSatisfaite :=
    match j.persistance with
    | PersistanceInjustice.episodique   => true   -- clôture directe
    | PersistanceInjustice.structurelle => false  -- porteur institutionnel requis
  }
  else j

/-- THÉORÈME 1 — Sens JE : si herméneutique + résistance bloquante,
    metaluciditeRequise = true et sourceResistanceDID renseigné. -/
theorem VJE_sensJE_declenche (j : EtatJustice) (did : String)
    (hType : j.typeInj = TypeInjustice.hermeneutique)
    (hResist : j.resistanceBloquante = true) :
    (appliquerSensJE j did).metaluciditeRequise = true ∧
    (appliquerSensJE j did).sourceResistanceDID = some did := by
  simp [appliquerSensJE, hType, hResist]

/-- THÉORÈME 2 — Sens EJ épisodique :
    si révision effectuée ET persistance épisodique,
    precondSatisfaite passe à true. -/
theorem VJE_sensEJ_episodique (e : EtatEvolutivite) (j : EtatJustice)
    (hRev : e.revisionEffectuee = true)
    (hPers : j.persistance = PersistanceInjustice.episodique) :
    (appliquerSensEJ e j).precondSatisfaite = true := by
  simp [appliquerSensEJ, hRev, hPers]

/-- THÉORÈME 3 — Sens EJ structurel :
    si révision effectuée ET persistance structurelle,
    precondSatisfaite reste false (porteur institutionnel requis).
    Formalise l'ENGAGEMENT SANS SYMÉTRIE levé (NT-G7 §9 lacune 4). -/
theorem VJE_sensEJ_structurel_bloque (e : EtatEvolutivite) (j : EtatJustice)
    (hRev : e.revisionEffectuee = true)
    (hPers : j.persistance = PersistanceInjustice.structurelle) :
    (appliquerSensEJ e j).precondSatisfaite = false := by
  simp [appliquerSensEJ, hRev, hPers]

-- ┌───────────────────────────────────────────────────────────────────┐
-- │ THÉORÈME 4 — REFONDÉ le 7 septembre 2026, décision du porteur      │
-- └───────────────────────────────────────────────────────────────────┘
--
-- L'ancien `VJE_commutatif` occupait cette place. Il énonçait :
--
--   let e  := { appliquerSensJE j did with revisionEffectuee := true }
--   let j' := appliquerSensEJ e j
--   j'.precondSatisfaite = match j.persistance with …
--
-- Le linter `unusedSimpArgs` a signalé que `appliquerSensJE` était un
-- argument `simp` INUTILE. La raison est structurelle :
--   · `appliquerSensEJ` ne lit QUE `e.revisionEffectuee` et
--     `j.persistance` ;
--   · le `with revisionEffectuee := true` ÉCRASE le seul champ que la
--     suite consulte ;
--   · donc `metaluciditeRequise` et `sourceResistanceDID`, tout ce que
--     la branche JE calcule, sont produits puis jetés.
--
-- RIEN DE LA BRANCHE JE N'ATTEINT LE RÉSULTAT. Le théorème ne
-- démontrait donc pas la commutativité du carré : il démontrait les
-- théorèmes 2 et 3 réunis, appliqués à un état dont la révision avait
-- été DÉCRÉTÉE dans l'énoncé.
--
-- [QUATRIÈME FORME DE SUR-REVENDICATION] — distincte des trois
-- inscrites en NT-ARCH §8bis : ni hypothèse inutilisée, ni hypothèse
-- reprise dans la conclusion, mais UNE HYPOTHÈSE INTRODUITE DANS LE
-- TERME MÊME DE L'ÉNONCÉ, par surcharge de champ. Aucun outil ne la
-- détecte ; seul l'avertissement `unusedSimpArgs` a servi de fil.
--
-- Le contenu réel est MEILLEUR que la revendication, et c'est ce qui
-- justifie la refondation plutôt qu'une suppression : que le carré ne
-- commute pas sans un acte de révision extérieur au calcul est
-- exactement ce que l'architecture soutient par ailleurs — une
-- révision est un acte, non une fonction. Le théorème le démontrait
-- sans le dire, en le supposant.

/-- **THÉORÈME 4a — le carré ne se ferme pas de lui-même.**

    Le chemin composé J→E→J laisse l'état de justice INCHANGÉ, parce
    que `appliquerSensJE` pose `revisionEffectuee := false` et que
    `appliquerSensEJ` prend alors sa branche `else`.

    C'est le résultat que l'ancien énoncé masquait. -/
theorem VJE_carre_ne_commute_pas_sans_revision (j : EtatJustice) (did : String) :
    appliquerSensEJ (appliquerSensJE j did) j = j := by
  simp [appliquerSensEJ, appliquerSensJE]

/-- **THÉORÈME 4b — ce que l'ancien énoncé démontrait, sous un nom qui
    le dit.** La révision est une PRÉMISSE, non un produit du carré.

    Noter ce qui a disparu : `did`, `hType`, `hResist` et
    `appliquerSensJE` lui-même. Aucun n'était nécessaire — leur
    présence dans l'ancien énoncé faisait croire que la branche JE
    contribuait au résultat. -/
theorem VJE_ferme_apres_revision_externe
    (j : EtatJustice) (e : EtatEvolutivite)
    (hRev : e.revisionEffectuee = true) :
    (appliquerSensEJ e j).precondSatisfaite =
      match j.persistance with
      | PersistanceInjustice.episodique   => true
      | PersistanceInjustice.structurelle => false := by
  simp [appliquerSensEJ, hRev]

/-- **THÉORÈME 4c — la branche JE ne produit pas la révision.**
    Un `rfl` qui inscrit le fait dont tout le reste découle. -/
-- [C-12 / R-5 — 28/09/2026] Garde de non-régression déclarée : la sortie
-- `revisionEffectuee` de `appliquerSensJE` est constante (`false`) par construction ;
-- il n'y a pas de témoin discriminant possible (R-7). Si la définition venait à
-- produire la révision, le carré J↔E se fermerait sans révision inscrite : c'est ce
-- que la garde interdit. Seule garde de PR-6 depuis le retrait du doublon.
theorem sensJE_ne_produit_pas_la_revision (j : EtatJustice) (did : String) :
    (appliquerSensJE j did).revisionEffectuee = false := rfl


/-- THÉORÈME 5 — Absence de déclenchement hors herméneutique :
    si typeInj ≠ HERMENEUTIQUE, metaluciditeRequise reste false.
    Empêche le sur-déclenchement de G-EVOLUTIVITE. -/
theorem VJE_pasDeJE_horsHermeneutique (j : EtatJustice) (did : String)
    (hType : j.typeInj ≠ TypeInjustice.hermeneutique) :
    (appliquerSensJE j did).metaluciditeRequise = false := by
  by_cases hEq : j.typeInj = TypeInjustice.hermeneutique
  · exact (False.elim (hType hEq))
  · simp [appliquerSensJE, hEq]


-- ┌───────────────────────────────────────────────────────────────────┐
-- │ PR-6 — `VJE_sansResistance` · versé le 8 septembre 2026            │
-- └───────────────────────────────────────────────────────────────────┘
--
-- PR-6 (Annexe §C-II.2) ferme la biconditionnelle AM-G7-04. Il est
-- versé ICI plutôt que dans un fichier propre — exception assumée à la
-- règle « un PR, un fichier, un namespace » que suivent PR-16 à PR-23 :
-- l'énoncé porte sur `appliquerSensJE`, et la biconditionnelle se lit
-- en regard des théorèmes 1 et 5, non trois fichiers plus loin.
--
-- LE CONTRÔLE DES NEUF A SONNÉ, ET AVANT LE VERSEMENT
-- ---------------------------------------------------
-- Une première rédaction énonçait `sourceResistanceDID = some did` :
-- l'audit d'axiomes a fait passer le compte de 9 à 10, `Classical.choice`
-- entrant par la comparaison d'égalité sur `String` — MÊME CAUSE QUE
-- PR-20 le matin même (§8quinquies). L'énoncé a été reformulé sur
-- `Option.isSome`, qui ne compare aucune chaîne. Deuxième déclenchement
-- du contrôle, deuxième fois sur les chaînes, et cette fois AVANT le
-- versement et non après.

/-- **PR-6 — sans résistance bloquante, pas de méta-lucidité.**
    Complète `VJE_pasDeJE_horsHermeneutique` (théorème 5), qui traitait
    l'autre disjonction. Empêche le sur-déclenchement de
    G-EVOLUTIVITE. -/
theorem VJE_sansResistance (j : EtatJustice) (did : String)
    (hResist : j.resistanceBloquante = false) :
    (appliquerSensJE j did).metaluciditeRequise = false := by
  simp [appliquerSensJE, hResist]

/-- Et le DID de source n'est pas renseigné non plus : le champ ne
    survit pas au non-déclenchement. -/
theorem VJE_sansResistance_sourceDID (j : EtatJustice) (did : String)
    (hResist : j.resistanceBloquante = false) :
    (appliquerSensJE j did).sourceResistanceDID = none := by
  simp [appliquerSensJE, hResist]

/-- **La biconditionnelle AM-G7-04, fermée.** `metaluciditeRequise` vaut
    `true` **si et seulement si** l'injustice est herméneutique ET la
    résistance bloquante.

    C'est ce que PR-6 apporte au-delà des deux implications : les
    théorèmes 1, 5 et `VJE_sansResistance` donnaient les trois cas un à
    un ; celui-ci dit qu'il n'y en a pas d'autre. -/
theorem VJE_metalucidite_ssi (j : EtatJustice) (did : String) :
    (appliquerSensJE j did).metaluciditeRequise = true
      ↔ (j.typeInj = TypeInjustice.hermeneutique ∧ j.resistanceBloquante = true) := by
  simp [appliquerSensJE]

/-- **Le DID de source suit exactement le déclenchement** — présent si
    et seulement si la méta-lucidité est requise.

    Énoncé sur `isSome` et non sur `= some did` : c'est ce qui garde le
    contrôle des neuf à neuf (voir l'encadré ci-dessus). Le fait que le
    DID inscrit soit bien celui passé en argument est déjà donné par le
    théorème 1, sous ses hypothèses. -/
theorem VJE_source_ssi_metalucidite (j : EtatJustice) (did : String) :
    (appliquerSensJE j did).sourceResistanceDID.isSome
      = (appliquerSensJE j did).metaluciditeRequise := by
  unfold appliquerSensJE
  by_cases hT : j.typeInj = TypeInjustice.hermeneutique
  · cases j.resistanceBloquante <;> simp [hT]
  · simp [hT]

/-! [C-12 — RETIRÉ LE 28/09/2026, décision du porteur] `PR6_ne_ferme_pas_le_carre`
    était le doublon exact de `sensJE_ne_produit_pas_la_revision` (même énoncé,
    même preuve `rfl`). La garde de PR-6 — fermer la biconditionnelle ne referme
    pas le carré — est portée par `sensJE_ne_produit_pas_la_revision`, seul cité
    par le set (NT-ARCH). Garde de non-régression déclarée : ne pas réintroduire ce théorème sous un autre nom. -/

end VJE
