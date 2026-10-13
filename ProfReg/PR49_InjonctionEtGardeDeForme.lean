/-
  PR-49 · La forme ne vaut pas réalisation ; l'injonction de vigilance
  ====================================================================

  Porteur : Pierre Musseau. Écrit le 30 septembre 2026, sur décisions
  D-ED-34 et D-ED-35, après lecture de Barraud de Lagerie (P.),
  « L'arbre des litiges à la loupe », Politix, 148, 2024/4, p. 119-146.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR48_QualificationDesPlaintes`.

  D-ED-34 — LA GARDE DE FORME
  ---------------------------
  L'article (d'après Edelman) décrit la « managérialisation » de la loi et
  la « déférence judiciaire » aux structures formelles : le juge retient
  qu'un plan comporte « les cinq items prévus par la loi suffisamment
  détaillés pour ne pas être regardés comme sommaires » (p. 138). Le
  Rana Plaza avait été inspecté l'année précédente (note 13).
  Garde : la CONFORMITÉ d'un protocole d'attestation (PR-45, CONV-17) ne
  vaut jamais CONSTAT DE RÉALISATION (PR-39). Les deux sont indépendants.

  D-ED-35 — L'INJONCTION DE VIGILANCE
  -----------------------------------
  Loi n° 2017-399, C. com. art. L.225-102-4, II (lu au JO du 28/03/2017) :
  mise en demeure, délai de trois mois, puis saisine par toute personne
  justifiant d'un intérêt à agir. L'article rapporte deux lectures de la
  mise en demeure, que le modèle garde en PARAMÈTRE `ExigenceGriefs` :
  · STRICTE — les griefs au jour des débats doivent être ceux de la mise
    en demeure (TJ Paris, réf., 28/02/2023, Total Ouganda) ;
  · SOUPLE — infirmée sur ce point par CA Paris, 18/06/2024 (Total Climat).
  `[NON VÉRIFIÉ EN SOURCE — décisions connues par l'article seul]`.
  Compétence : tribunal judiciaire de Paris depuis la loi du 22/12/2021
  (idem, non lue).

  CE QUE LE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne dit pas ce qu'est un plan « effectif » : c'est le jugement que la
    garde protège, non qu'elle remplace.
  · Il ne modélise ni le référé ni l'action en responsabilité (L.225-102-5).
-/

import ProfReg.PR48_QualificationDesPlaintes

namespace ProfRegPR49

open ProfRegPR35 (Entite)
open ProfRegPR39 (LigneRealisation EtatResultat etat effortSeul constatRiverain entreprise)
open ProfRegPR43 (DesignationControle)
open ProfRegPR44 (Saisine Voie Qualite saisineRecevable)
open ProfRegPR45 (Protocole conforme protoConforme protoSansDemande)

/-! ## 1. D-ED-34 — la conformité ne vaut pas réalisation -/

/-- **Garde générale** : sans constat de réalisation, l'état reste
    « attendu », quelle que soit la conformité du protocole. -/
theorem la_conformite_ne_vaut_pas_realisation (ds : List DesignationControle) (r : Entite)
    (p : Protocole) (l : LigneRealisation) (b : Entite)
    (_hc : conforme ds r p = true) (h : l.constat = none) :
    etat l b = .attendu := by
  simp [etat, h]

open ProfRegPR44 (riviere dsRiviere)

/-- **Indépendance** (témoin R-7) : protocole conforme sans réalisation
    constatée ; protocole non conforme avec réalisation constatée. -/
theorem conformite_et_realisation_independantes :
    conforme dsRiviere riviere protoConforme = true
    ∧ etat effortSeul ProfRegPR39.riviere = .attendu
    ∧ conforme dsRiviere riviere protoSansDemande = false
    ∧ etat constatRiverain ProfRegPR39.riviere = .constate := by
  decide

/-! ## 2. D-ED-35 — l'injonction de vigilance -/

inductive ExigenceGriefs where
  | stricte   -- TJ Paris, réf., 28/02/2023
  | souple    -- CA Paris, 18/06/2024
  deriving DecidableEq, Repr

structure MiseEnDemeure where
  faite            : Bool
  moisEcoules      : Nat
  /-- Les griefs au jour des débats sont ceux de la mise en demeure. -/
  griefsIdentiques : Bool
  deriving DecidableEq, Repr

/-- **Recevabilité de l'injonction.** -/
def injonctionRecevable (ex : ExigenceGriefs) (s : Saisine) (md : MiseEnDemeure) : Bool :=
  decide (s.voie = .injonctionVigilance) && saisineRecevable s && md.faite
  && decide (3 ≤ md.moisEcoules)
  && (match ex with | .stricte => md.griefsIdentiques | .souple => true)

/-- **Sans mise en demeure, irrecevable.** -/
theorem sans_mise_en_demeure_irrecevable (ex : ExigenceGriefs) (s : Saisine) (m : Nat) (g : Bool) :
    injonctionRecevable ex s ⟨false, m, g⟩ = false := by
  simp [injonctionRecevable]

/-- **Avant trois mois, irrecevable.** -/
theorem avant_trois_mois_irrecevable (ex : ExigenceGriefs) (s : Saisine) (g : Bool) :
    injonctionRecevable ex s ⟨true, 2, g⟩ = false := by
  simp [injonctionRecevable]

def saisineAsso : Saisine := ⟨.injonctionVigilance, .interetAAgir, false, none⟩
def mdAncienne : MiseEnDemeure := ⟨true, 36, false⟩   -- griefs actualisés depuis

/-- **PR-49 (1) — la jurisprudence comme paramètre** : sur la même saisine
    et la même mise en demeure, la lecture stricte ferme ce que la lecture
    souple ouvre. Ni l'une ni l'autre ne dépend du consentement de la société. -/
theorem la_lecture_stricte_ferme_ce_que_la_souple_ouvre :
    injonctionRecevable .stricte saisineAsso mdAncienne = false
    ∧ injonctionRecevable .souple saisineAsso mdAncienne = true := by
  decide

/-- **PR-49 (2) — l'intérêt à agir est requis.** -/
theorem sans_interet_a_agir_irrecevable :
    injonctionRecevable .souple ⟨.injonctionVigilance, .quelconque, false, none⟩ mdAncienne = false
    ∧ injonctionRecevable .souple ⟨.parquet, .interetAAgir, false, none⟩ mdAncienne = false := by
  decide

/-- **Témoin discriminant** (R-7) de `injonctionRecevable`. -/
theorem injonction_temoin_discriminant :
    injonctionRecevable .stricte saisineAsso ⟨true, 3, true⟩ = true
    ∧ injonctionRecevable .stricte saisineAsso ⟨true, 2, true⟩ = false
    ∧ injonctionRecevable .stricte saisineAsso ⟨false, 3, true⟩ = false
    ∧ injonctionRecevable .stricte saisineAsso ⟨true, 3, false⟩ = false := by
  decide

end ProfRegPR49
