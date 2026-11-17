/-
  PR-37 · Le registre d'un milieu ou d'un collectif : déclaré par les concernés,
          portant le maintien
  ================================================================================

  Porteur : Pierre Musseau. Écrit le 29 septembre 2026, sur décision D-ED-9.
  Révisé le 30 septembre 2026 : D-ED-16 (§2, maintien CONV-11) et D-ED-14
  (§1, déclaration des concernés).
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR35_EcritureDuale`,
  `ProfReg.PR23_MouvementDeMaintien` et `ProfReg.PR31_BonneFormationDeclarative`.

  LA DÉCISION DU PORTEUR (D-ED-9, 29/09/2026)
  -------------------------------------------
  « Qui tient le registre d'un milieu : cela passe par la déclaration des
    concernés (AX-7) et la création d'un registre associé qui porte le
    maintien du milieu. »

  CE QUE LE FICHIER EN RETIENT
  ----------------------------
  1. Le registre a un TITULAIRE (c'est envers lui que les autres entités
     inscrivent) et un ÉCRIVANT désigné par une DÉCLARATION DES CONCERNÉS —
     le « triplet porteur » de NT-ARCH §8.5 : « l'entité, la personne qui
     inscrit, et le rôle qui l'y habilite ».
  2. La déclaration vaut si elle est ARRÊTÉE par les concernés, non
     seulement RATIFIÉE (condition de réfutation de AX-7). `nonDeclare` refuse.
  3. Le registre PORTE LE MAINTIEN : `ProfRegPR23.MaintienCONV11`, six
     éléments, solde calculé, registre nommé vérifié (D-ED-16).
  4. Sans registre bien formé, ce qu'une entité inscrit envers le titulaire
     RESTE EN ÉCART (D-ED-3).

  RÉVISION D-ED-14 (30/09/2026) — LA DÉCLARATION DES CONCERNÉS
  -------------------------------------------------------------
  Note `Note_Ecriture_Duale_Points_Ouverts_x_Cinq_Situations_2026-09-30.md`,
  point (β) et situations S4, S5. La déclaration porte désormais :
  (i)   un CRITÈRE D'INCLUSION, non une liste close — les concernés présents
        à la date sont une donnée, la règle qui dit qui l'est est déclarée
        (leçon de PR-22 : une énumération close exclut toujours quelqu'un) ;
  (ii)  le MODE (arrêtée / ratifiée / non déclarée), comme avant ;
  (iii) un HORIZON DE RÉEXAMEN : échue, la déclaration cesse de fonder le
        registre et l'écart revient — « regularly re-assessed by its
        representatives » (Rambaud & Richard 2015, p. 98) ; contre la « perte
        de bouclage » (Vuattoux, chap. 2) ;
  (iv)  un INTERPRÈTE, qui DÉCRIT l'état à maintenir, distinct de ceux qui
        ARRÊTENT : les « representatives or spokespersons » de Rambaud &
        Richard ne sont pas les concernés de AX-7. Raccord à `InscriptionMilieu`
        de PR-31 (champ I, NT-G5 A-TÉTRA-3) ;
  (v)   la NATURE DU TITULAIRE : un milieu n'écrit pas son registre (écrivant
        désigné, distinct) ; un collectif humain PEUT l'écrire lui-même (ses
        instances). Avant D-ED-14, PR-37 interdisait tout titulaire écrivant,
        ce qui excluait un collectif d'employés de son propre registre
        `[INCOHÉRENCE INTER-COUCHES — niveau 0, levée]`.

  `[TRANSPOSITION DÉCLARÉE]` AX-7 constate que des concernés PEUVENT arrêter
  les critères d'un seuil. L'étendre à la désignation de l'écrivant d'un
  registre est une décision du porteur, non une conséquence de AX-7.

  CE QUE LE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne dit pas QUI sont les concernés : le critère d'inclusion est une
    donnée déclarée ; le modèle vérifie qu'il existe, non qu'il est juste.
  · Il ne vérifie pas que le maintien est RÉALISÉ : c'est PR-39 (D-ED-15).
  · Il ne qualifie pas l'écart (constaté, non vérifiable, contesté) : c'est
    PR-40 (D-ED-13).
-/

import ProfReg.PR35_EcritureDuale
import ProfReg.PR23_MouvementDeMaintien
import ProfReg.PR31_BonneFormationDeclarative

namespace ProfRegPR37

open ProfRegPR35
open ProfRegPR23 (MaintienCONV11 Situation)

/-! ## 1. La déclaration des concernés (AX-7 ; révisée D-ED-14) -/

/-- Le mode d'adoption. La distinction `arretee` / `ratifiee` est la
    condition de réfutation de AX-7. -/
inductive ModeDeclaration where
  | arretee     -- les concernés arrêtent eux-mêmes la désignation
  | ratifiee    -- une équipe propose, les concernés ratifient
  | nonDeclare  -- refuse, n'autorise pas (patron CONV-9)
  deriving DecidableEq, Repr

/-- La nature du titulaire : un milieu n'écrit pas son registre, un
    collectif humain peut l'écrire (D-ED-14 (v)). -/
inductive NatureTitulaire where
  | milieu
  | collectifHumain
  deriving DecidableEq, Repr

structure DeclarationConcernes where
  titulaire  : Entite
  nature     : NatureTitulaire
  /-- La règle qui dit qui est concerné, déclarée (code). `none` : liste
      close sans règle — refusée. -/
  inclusion  : Option Nat
  /-- Les concernés qui ont arrêté la déclaration, à sa date. -/
  concernes  : List Entite
  ecrivant   : Entite
  /-- Qui décrit l'état à maintenir (champ I de PR-31). -/
  interprete : Option Entite
  mode       : ModeDeclaration
  /-- Date limite de réexamen. `none` : aucun réexamen prévu — refusé. -/
  reexamen   : Option Nat
  deriving Repr

/-- L'écrivant est admissible au regard de la nature du titulaire. -/
def ecrivantAdmissible (d : DeclarationConcernes) : Bool :=
  match d.nature with
  | .milieu          => !(d.ecrivant == d.titulaire)
  | .collectifHumain => true

/-- La déclaration n'est pas échue à la date `t`. -/
def enVigueur (d : DeclarationConcernes) (t : Nat) : Bool :=
  match d.reexamen with
  | some h => decide (t ≤ h)
  | none   => false

/-- **Déclaration valide à la date `t`.** -/
def declarationValide (d : DeclarationConcernes) (t : Nat) : Bool :=
  decide (d.mode = .arretee) && !d.concernes.isEmpty && d.inclusion.isSome
    && d.interprete.isSome && ecrivantAdmissible d && enVigueur d t

/-- **Raccord PR-31** : la déclaration fournit le déclarant (l'écrivant) et
    l'interprète d'une `InscriptionMilieu` ; S et P viennent de l'inscription
    elle-même. -/
def versInscriptionMilieu (d : DeclarationConcernes) (s p : Option Nat) :
    ProfRegPR31.InscriptionMilieu :=
  ⟨d.ecrivant, s, p, d.interprete⟩

/-! ## 2. Le maintien structuré (CONV-11 ; D-ED-16) -/

/-- Le maintien d'un registre : la structure unique de CONV-11. -/
abbrev MaintienMilieu := MaintienCONV11 Entite Entite Nat

/-! ## 3. Le registre associé -/

structure RegistreDuMilieu (V : Type) where
  declaration  : DeclarationConcernes
  registre     : Registre V
  titulaire_ok : registre.teneur = declaration.titulaire
  maintien     : Option MaintienMilieu

/-- **Bien formé à la date `t`** : déclaration valide et en vigueur,
    maintien inscrit, et le maintien nomme ce registre-ci. -/
def bienForme {V : Type} (R : RegistreDuMilieu V) (t : Nat) : Bool :=
  declarationValide R.declaration t &&
    match R.maintien with
    | some m => m.registre == R.declaration.titulaire
    | none   => false

def registreOpposable {V : Type} (t : Nat) : Option (RegistreDuMilieu V) → Option (Registre V)
  | none   => none
  | some r => if bienForme r t then some r.registre else none

/-- **L'écart envers le titulaire, à la date `t`.** -/
def ecartEnversMilieu {V : Type} (t : Nat) (RA : Registre V) (m : Entite)
    (R : Option (RegistreDuMilieu V)) : List (Ligne V) :=
  match registreOpposable t R with
  | some rb => ecart RA rb
  | none    => RA.lignes.filter (fun l => l.contrepartie == m)

/-! ## 4. Ce qui se démontre -/

theorem sans_registre_l_ecart_reste_inscrit {V : Type} (t : Nat) (RA : Registre V) (m : Entite) :
    ecartEnversMilieu t RA m none = RA.lignes.filter (fun l => l.contrepartie == m) := rfl

/-- **La ratification ne fonde pas le registre** (AX-7). -/
theorem la_ratification_ne_fonde_pas_le_registre {V : Type} (t : Nat) (r : RegistreDuMilieu V)
    (h : r.declaration.mode = .ratifiee) : registreOpposable t (some r) = none := by
  simp [registreOpposable, bienForme, declarationValide, h]

/-- **Sans déclaration, pas de registre** (`nonDeclare` refuse). -/
theorem sans_declaration_pas_de_registre {V : Type} (t : Nat) (r : RegistreDuMilieu V)
    (h : r.declaration.mode = .nonDeclare) : registreOpposable t (some r) = none := by
  simp [registreOpposable, bienForme, declarationValide, h]

/-- **Sans critère d'inclusion, pas de registre** (D-ED-14 (i)). -/
theorem sans_critere_d_inclusion_pas_de_registre {V : Type} (t : Nat) (r : RegistreDuMilieu V)
    (h : r.declaration.inclusion = none) : registreOpposable t (some r) = none := by
  simp [registreOpposable, bienForme, declarationValide, h]

/-- **Sans interprète, pas de registre** (D-ED-14 (iv)). -/
theorem sans_interprete_pas_de_registre {V : Type} (t : Nat) (r : RegistreDuMilieu V)
    (h : r.declaration.interprete = none) : registreOpposable t (some r) = none := by
  simp [registreOpposable, bienForme, declarationValide, h]

/-- **Et c'est le marqueur de PR-31** : S et P renseignés, sans interprète,
    l'inscription de milieu que la déclaration engendre lève
    `[INSCRIPTION DE MILIEU SANS INTERPRÈTE]`. -/
theorem sans_interprete_le_marqueur_PR31_se_leve (d : DeclarationConcernes) (s p : Nat)
    (h : d.interprete = none) :
    ProfRegPR31.marqueurSansInterprete (versInscriptionMilieu d (some s) (some p)) = true := by
  simp [ProfRegPR31.marqueurSansInterprete, versInscriptionMilieu, h]

/-- **Sans maintien inscrit : pas d'appui** (CONV-11, E4). -/
theorem sans_maintien_pas_d_appui {V : Type} (t : Nat) (r : RegistreDuMilieu V)
    (h : r.maintien = none) : registreOpposable t (some r) = none := by
  simp [registreOpposable, bienForme, h]

/-- **Un maintien qui nomme un autre registre : pas d'appui** (D-ED-16). -/
theorem maintien_d_un_autre_registre_pas_d_appui {V : Type} (t : Nat) (r : RegistreDuMilieu V)
    (m : MaintienMilieu) (hm : r.maintien = some m)
    (h : m.registre ≠ r.declaration.titulaire) : registreOpposable t (some r) = none := by
  have hb : (m.registre == r.declaration.titulaire) = false := by
    cases hq : (m.registre == r.declaration.titulaire) with
    | false => rfl
    | true => exact absurd (of_decide_eq_true hq) h
  simp [registreOpposable, bienForme, hm, hb]

/-- **Un milieu n'écrit pas lui-même son registre** — désormais borné à la
    nature `milieu` (D-ED-14 (v)). -/
theorem le_milieu_n_ecrit_pas_son_registre {V : Type} (t : Nat) (r : RegistreDuMilieu V)
    (hn : r.declaration.nature = .milieu) (h : bienForme r t = true) :
    r.declaration.ecrivant ≠ r.declaration.titulaire := by
  intro he
  unfold bienForme declarationValide ecrivantAdmissible at h
  rw [hn, he] at h
  have : (r.declaration.titulaire == r.declaration.titulaire) = true := decide_eq_true rfl
  rw [this] at h
  simp at h

/-! ## 5. Instance : une entreprise et une rivière -/

def entreprise : Entite := 2
def riviere    : Entite := 10
def collectifRiverain : Entite := 13
def hydrologue : Entite := 14

/-- La déclaration pour la rivière : titulaire la rivière (milieu) ; critère
    d'inclusion déclaré (code 1) ; concernés 11 et 12 ; écrivant le collectif
    riverain ; interprète un hydrologue, qui n'est pas un concerné ; réexamen
    avant 2030. -/
def declRiviere (mode : ModeDeclaration) : DeclarationConcernes :=
  ⟨riviere, .milieu, some 1, [11, 12], collectifRiverain, some hydrologue, mode, some 2030⟩

def maintienRiviere : MaintienMilieu :=
  ⟨collectifRiverain, entreprise, riviere, ⟨100, 60⟩, 2030, 1⟩

def registreEntreprise : Registre Nat := ⟨entreprise, [⟨riviere, .Dplus, 100⟩]⟩

def registreRiviere (d : DeclarationConcernes) (hd : d.titulaire = riviere)
    (m : Option MaintienMilieu) : RegistreDuMilieu Nat :=
  ⟨d, ⟨riviere, [⟨entreprise, .Cplus, 100⟩]⟩, hd.symm, m⟩

def regR (mode : ModeDeclaration) : RegistreDuMilieu Nat :=
  registreRiviere (declRiviere mode) rfl (some maintienRiviere)

/-- **PR-37 — écriture duale avec un milieu**, en 2026. -/
theorem ecriture_duale_avec_un_milieu :
    bienForme (regR .arretee) 2026 = true
    ∧ EcritureDuale registreEntreprise (regR .arretee).registre
    ∧ ecartEnversMilieu 2026 registreEntreprise riviere (some (regR .arretee)) = [] := by
  decide

/-- **Témoin discriminant** (R-7) : arrêtée, l'écart est vide ; ratifiée, il
    reste. -/
theorem registre_de_milieu_temoin_discriminant :
    ecartEnversMilieu 2026 registreEntreprise riviere (some (regR .arretee)) = []
    ∧ ecartEnversMilieu 2026 registreEntreprise riviere (some (regR .ratifiee)) ≠ [] := by
  decide

/-- **Déclaration échue, l'écart revient** (D-ED-14 (iii)) : le même
    registre fonde l'écriture duale en 2026, plus en 2031 si la déclaration
    n'a pas été réexaminée. -/
theorem declaration_echue_l_ecart_revient :
    ecartEnversMilieu 2026 registreEntreprise riviere (some (regR .arretee)) = []
    ∧ ecartEnversMilieu 2031 registreEntreprise riviere (some (regR .arretee)) ≠ [] := by
  decide

/-- **L'interprète n'est pas un concerné** (D-ED-14 (iv)) : dans une
    déclaration valide, celui qui décrit l'état à maintenir peut ne pas
    figurer parmi ceux qui arrêtent. Les deux rôles ne se déduisent pas l'un
    de l'autre. -/
theorem l_interprete_n_est_pas_un_concerne :
    declarationValide (declRiviere .arretee) 2026 = true
    ∧ hydrologue ∉ (declRiviere .arretee).concernes := by
  decide

/-- Si le maintien nomme un autre registre, l'écart revient (D-ED-16). -/
theorem registre_mal_nomme_l_ecart_revient :
    ecartEnversMilieu 2026 registreEntreprise riviere
      (some (registreRiviere (declRiviere .arretee) rfl
        (some ⟨collectifRiverain, entreprise, entreprise, ⟨100, 60⟩, 2030, 1⟩))) ≠ [] := by
  decide

/-- La dette de préservation de la rivière est calculée : 100 dus, 60 engagés. -/
theorem la_dette_de_preservation_du_milieu_est_calculee :
    maintienRiviere.solde = 40 := by
  decide

/-! ## 6. Instance : une entreprise et un collectif d'employés (D-ED-14 (v)) -/

def collectifEmployes : Entite := 30
def cse : Entite := 31

/-- Le collectif tient **lui-même** son registre (écrivant = titulaire) ;
    l'interprète est l'instance représentative (CSE). -/
def declCollectif (nature : NatureTitulaire) : DeclarationConcernes :=
  ⟨collectifEmployes, nature, some 2, [32, 33, 34], collectifEmployes, some cse, .arretee, some 2027⟩

/-- **Un collectif humain peut tenir son propre registre ; un milieu non.**
    La même déclaration, écrivant = titulaire, est valide pour un collectif
    et refusée pour un milieu. -/
theorem un_collectif_peut_tenir_son_propre_registre :
    declarationValide (declCollectif .collectifHumain) 2026 = true
    ∧ declarationValide (declCollectif .milieu) 2026 = false := by
  decide

end ProfRegPR37
