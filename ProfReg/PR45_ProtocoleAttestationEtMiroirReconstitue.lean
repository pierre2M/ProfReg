/-
  PR-45 · Protocole d'attestation, CONV-17, miroir reconstitué
  ============================================================

  Porteur : Pierre Musseau. Écrit le 30 septembre 2026, sur décisions
  D-ED-22 (arrêter le protocole d'attestation), D-ED-23 (instituer CONV-17)
  et D-ED-24 (reconstituer partiellement le miroir par l'information
  environnementale). Note : `Note_D-ED-21_…` §6. Annexe §A.15.13 (CONV-17).
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR44_ConstatUnilateralEtTiersExterieur`.

  D-ED-22 — LE PROTOCOLE
  ----------------------
  Une attestation n'est une attestation que si elle suit le protocole :
    1. la LIGNE visée (contrepartie, nature, quantité) ;
    2. des PIÈCES tracées — auteur et méthode déclarés ;
    3. l'instance DÉSIGNÉE (arrêtée) par le registre, ni teneur ni X (PR-44) ;
    4. la déclaration de NON-LIAISON de l'instance envers X ;
    5. l'attestation est SANS QUALIFICATION juridique (homologue du
       « exclusives de tout avis » du commissaire de justice) ;
    6. la DEMANDE DE COMMUNICATION adressée à X, et sa réponse (PR-40) ;
    7. la CONFRONTATION au miroir reconstitué (D-ED-24), fût-elle
       « non obtenue » — elle est toujours écrite (champ non optionnel).

  D-ED-23 — CONV-17
  -----------------
  « Seul un constat attesté selon le protocole est porté AU NOM du
  registre. » Une saisine au nom du registre sans protocole conforme est
  inscrite `horsProtocole` (marqueur `[SAISINE HORS PROTOCOLE]`).
  CONV-17 n'interdit à PERSONNE de signaler : un membre signale en son nom,
  hors registre.

  D-ED-24 — LE MIROIR RECONSTITUÉ
  -------------------------------
  X ne tient pas de registre, mais il DÉCLARE à l'administration (moyens de
  mesure, L.214-8 C. env.) ; ces données s'obtiennent auprès de l'autorité
  qui les détient (L.124-1 s.). La ligne de la rivière est CONFRONTÉE à la
  déclaration de X : concordante, sous-déclarée (de d), sur-déclarée (de d),
  ou non obtenue. La reconstitution suppose un DÉTENTEUR TIERS : ce que X
  communique lui-même relève de PR-40, non d'ici.
  La confrontation ne fait pas une écriture duale : X n'a rien écrit dans un
  registre de communalité. Elle ne change ni la ligne ni son statut.

  CE QUE LE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne vérifie ni la méthode, ni la sincérité de la non-liaison : déclarées.
  · Il ne dit pas quelle force a la déclaration de X devant un juge.
  · Il ne tolère aucun arrondi : la concordance est l'égalité des montants.
-/

import ProfReg.PR44_ConstatUnilateralEtTiersExterieur

namespace ProfRegPR45

open ProfRegPR35 (Entite Ligne)
open ProfRegPR43 (DesignationControle)
open ProfRegPR40 (Communication)
open ProfRegPR44 (Piece Attestation attestationValide Saisine StatutConstat statutConstat)

/-! ## 1. D-ED-24 — le miroir reconstitué -/

/-- Une déclaration de X à l'administration, obtenue auprès de son détenteur. -/
structure DeclarationAdministrative where
  declarant : Entite
  detenteur : Entite
  montant   : Nat
  deriving DecidableEq, Repr

inductive Confrontation where
  | concordant
  | sousDeclare (d : Nat)
  | surDeclare  (d : Nat)
  | nonObtenue
  deriving DecidableEq, Repr

/-- Confronter la ligne du registre à la déclaration de sa contrepartie. -/
def confronter (l : Ligne Nat) (d : Option DeclarationAdministrative) : Confrontation :=
  match d with
  | none => .nonObtenue
  | some dec =>
    if dec.declarant == l.contrepartie && !(dec.detenteur == dec.declarant) then
      if dec.montant == l.montant then .concordant
      else if dec.montant < l.montant then .sousDeclare (l.montant - dec.montant)
      else .surDeclare (dec.montant - l.montant)
    else .nonObtenue

/-! ## 2. D-ED-22 — le protocole d'attestation -/

structure PieceTracee where
  piece           : Piece
  auteur          : Entite
  methodeDeclaree : Bool
  deriving DecidableEq, Repr

structure Protocole where
  ligne                : Ligne Nat
  instanceCtrl         : Entite
  tracees              : List PieceTracee
  nonLiaisonDeclaree   : Bool
  sansQualification    : Bool
  demandeCommunication : Option Communication
  confrontation        : Confrontation
  deriving DecidableEq, Repr

/-- L'attestation (au sens de PR-44) que porte le protocole. -/
def attestationDe (p : Protocole) : Attestation :=
  ⟨p.instanceCtrl, p.tracees.map (·.piece)⟩

/-- **Le protocole est conforme** (rubriques 1 à 7). -/
def conforme (ds : List DesignationControle) (reg : Entite) (p : Protocole) : Bool :=
  attestationValide ds reg p.ligne.contrepartie (attestationDe p)
  && !p.tracees.isEmpty
  && p.tracees.all (·.methodeDeclaree)
  && p.nonLiaisonDeclaree
  && p.sansQualification
  && p.demandeCommunication.isSome

/-! ## 3. D-ED-23 — CONV-17 -/

inductive Emetteur where
  | registre
  | membre (e : Entite)
  deriving DecidableEq, Repr

inductive StatutSaisine where
  | auNomDuRegistre (s : StatutConstat)
  | horsProtocole                 -- [SAISINE HORS PROTOCOLE]
  | signalementIndividuel (e : Entite)
  deriving DecidableEq, Repr

/-- **CONV-17.** -/
def statut17 (ds : List DesignationControle) (reg : Entite) (p : Protocole)
    (em : Emetteur) (sais : Option Saisine) : StatutSaisine :=
  match em with
  | .membre e => .signalementIndividuel e
  | .registre =>
    if conforme ds reg p then
      .auNomDuRegistre (statutConstat ds reg p.ligne.contrepartie (some (attestationDe p)) sais)
    else
      match sais with
      | none   => .auNomDuRegistre .unilateral
      | some _ => .horsProtocole

/-! ## 4. Ce qui se démontre (général) -/

/-- **CONV-17 (1) — sans protocole, rien n'est porté au nom du registre.** -/
theorem conv17_sans_protocole_hors_protocole (ds : List DesignationControle) (reg : Entite)
    (p : Protocole) (s : Saisine) (h : conforme ds reg p = false) :
    statut17 ds reg p .registre (some s) = .horsProtocole := by
  simp [statut17, h]

/-- **CONV-17 (2) — CONV-17 n'interdit pas le signalement individuel.** -/
theorem conv17_n_interdit_pas_de_signaler (ds : List DesignationControle) (reg : Entite)
    (p : Protocole) (e : Entite) (sais : Option Saisine) :
    statut17 ds reg p (.membre e) sais = .signalementIndividuel e := rfl

/-- **CONV-17 (3) — avec protocole, on retrouve PR-44.** -/
theorem conv17_avec_protocole_retrouve_PR44 (ds : List DesignationControle) (reg : Entite)
    (p : Protocole) (sais : Option Saisine) (h : conforme ds reg p = true) :
    statut17 ds reg p .registre sais
      = .auNomDuRegistre (statutConstat ds reg p.ligne.contrepartie (some (attestationDe p)) sais) := by
  simp [statut17, h]

/-- **D-ED-24 — la reconstitution suppose un détenteur tiers** : une
    « déclaration » détenue par X lui-même n'est pas un miroir reconstitué. -/
theorem la_reconstitution_suppose_un_detenteur_tiers (l : Ligne Nat) (m : Nat) :
    confronter l (some ⟨l.contrepartie, l.contrepartie, m⟩) = .nonObtenue := by
  have h : (l.contrepartie == l.contrepartie) = true := decide_eq_true rfl
  show (if ((l.contrepartie == l.contrepartie) && !(l.contrepartie == l.contrepartie)) = true
        then _ else _) = _
  rw [h]; rfl

/-! ## 5. Instance : la rivière et X -/

open ProfRegPR44 (riviere entrepriseX comiteDuFleuve dsRiviere ligneX)

def prefet : Entite := 90
def hydrologue : Entite := 14

/-- X a déclaré 80 à l'administration ; la rivière constate 120. -/
def declX : DeclarationAdministrative := ⟨entrepriseX, prefet, 80⟩

def protoConforme : Protocole :=
  { ligne := ligneX, instanceCtrl := comiteDuFleuve
    tracees := [⟨.mesureInterne, riviere, true⟩, ⟨.rapportExpert, hydrologue, true⟩]
    nonLiaisonDeclaree := true, sansQualification := true
    demandeCommunication := some .refuse
    confrontation := confronter ligneX (some declX) }

def protoSansDemande : Protocole := { protoConforme with demandeCommunication := none }
def protoQualifiant  : Protocole := { protoConforme with sansQualification := false }
def protoSansMethode : Protocole :=
  { protoConforme with tracees := [⟨.mesureInterne, riviere, false⟩] }

/-- **PR-45 (1) — la sous-déclaration est chiffrée** : 120 constatés, 80
    déclarés par X lui-même : écart de 40. -/
theorem la_sous_declaration_est_chiffree :
    confronter ligneX (some declX) = .sousDeclare 40
    ∧ protoConforme.confrontation = .sousDeclare 40 := by
  decide

/-- **PR-45 (2) — le protocole conforme porte ; chaque rubrique manquante
    fait tomber la saisine hors protocole.** -/
theorem chaque_rubrique_compte :
    statut17 dsRiviere riviere protoConforme .registre
        (some ⟨.autoriteAdministrative, .quelconque, false, none⟩)
      = .auNomDuRegistre (.porte .autoriteAdministrative)
    ∧ statut17 dsRiviere riviere protoSansDemande .registre
        (some ⟨.autoriteAdministrative, .quelconque, false, none⟩) = .horsProtocole
    ∧ statut17 dsRiviere riviere protoQualifiant .registre
        (some ⟨.autoriteAdministrative, .quelconque, false, none⟩) = .horsProtocole
    ∧ statut17 dsRiviere riviere protoSansMethode .registre
        (some ⟨.autoriteAdministrative, .quelconque, false, none⟩) = .horsProtocole := by
  decide

/-- **PR-45 (3) — un membre signale quand même** ; son signalement n'est pas
    inscrit comme porté au nom du registre. -/
theorem le_membre_signale_hors_registre :
    statut17 dsRiviere riviere protoSansDemande (.membre hydrologue)
        (some ⟨.parquet, .quelconque, false, none⟩) = .signalementIndividuel hydrologue := by
  decide

/-- **Témoin discriminant** (R-7) de `confronter` : les quatre issues. -/
theorem confronter_temoin_discriminant :
    confronter ligneX (some ⟨entrepriseX, prefet, 120⟩) = .concordant
    ∧ confronter ligneX (some ⟨entrepriseX, prefet, 80⟩) = .sousDeclare 40
    ∧ confronter ligneX (some ⟨entrepriseX, prefet, 150⟩) = .surDeclare 30
    ∧ confronter ligneX none = .nonObtenue := by
  decide

/-- **Témoin discriminant** (R-7) de `conforme`. -/
theorem conforme_temoin_discriminant :
    conforme dsRiviere riviere protoConforme = true
    ∧ conforme dsRiviere riviere protoSansDemande = false := by
  decide

end ProfRegPR45
