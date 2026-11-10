/-
  PR-44 · Le constat unilatéral : attestation interne, puis tiers extérieur
  ========================================================================

  Porteur : Pierre Musseau. Écrit le 30 septembre 2026, sur décision D-ED-21
  (« instruis les points 1 et 2 »). Note associée :
  `Note_D-ED-21_Constat_Unilateral_Voies_Privee_Publique_2026-09-30.md`.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR43_InstanceDeControle`.

  LA SITUATION
  ------------
  Une rivière a un registre de communalité, une instance de contrôle (le
  comité du fleuve). L'entreprise X prélève et pollue ; elle REFUSE de
  participer et de tenir un registre. Le registre de la rivière porte une
  ligne envers X, sans miroir : statut `refuse` (PR-40). X n'a désigné
  aucune instance : l'écart n'est PAS ARBITRABLE en interne (PR-43).

  CE QUE LE FICHIER AJOUTE
  ------------------------
  POINT 1 — l'ATTESTATION INTERNE. L'instance de contrôle désignée (arrêtée)
  par le registre de la rivière atteste la ligne, sur pièces. Elle en fixe
  la QUALITÉ DE PREUVE ; elle ne tranche rien envers X.
  POINT 2 — le statut « PORTÉ DEVANT UN TIERS EXTÉRIEUR ». Le constat attesté
  est porté par une VOIE : privée (négociation, transaction — art. 2044
  C. civ. ; arbitrage — D-ED-29), ou publique (juge judiciaire du préjudice
  écologique — art. 1246 à 1248 C. civ. ; autorité administrative de police
  de l'eau — art. L.171-8 C. env. ; parquet — art. 40 CPP, délit de l'art.
  L.216-6 C. env. ; autorité de supervision — CS3D art. 26, D-ED-30 ;
  injonction de vigilance — C. com. L.225-102-4 II, D-ED-35). [D-ED-37 — 30/09/2026] :
  huit voies, huit constructeurs de `Voie`.

  LA RÈGLE FORMALISÉE
  -------------------
  1. L'attestation interne ne tranche pas envers X (X n'a rien désigné).
  2. Sans pièce extérieure, l'attestation ne fait pas « foi jusqu'à preuve
     contraire » : le registre ne se constitue pas de titre à lui-même
     (art. 1363 C. civ.) ; il reste admissible comme preuve d'un fait
     (art. 1358 : « la preuve peut être apportée par tout moyen »).
  3. Le constat d'un commissaire de justice fait foi jusqu'à preuve contraire
     SAUF en matière pénale, où il vaut « simples renseignements »
     (ord. n° 2016-728, art. 1).
  4. Les voies privées exigent le CONSENTEMENT de X ; les voies publiques
     NON. Le juge du préjudice écologique exige la QUALITÉ du demandeur
     (art. 1248).
  5. Porté n'est pas tranché ; tranché n'efface rien : la ligne reste
     inscrite, avec l'issue.
  6. [CHOIX DE CONCEPTION] Seul un constat ATTESTÉ est porté au nom du
     registre. Le droit n'impose pas cette condition (n'importe qui peut
     signaler) : c'est une discipline du registre.

  AJOUT D-ED-35 (30/09/2026, décision du porteur)
  -----------------------------------------------
  Voie `injonctionVigilance` : l'action en injonction de la loi
  n° 2017-399 (C. com. art. L.225-102-4, II) — « la juridiction compétente
  peut, à la demande de toute personne justifiant d'un intérêt à agir, lui
  enjoindre, le cas échéant sous astreinte, de les respecter », après une
  mise en demeure restée sans effet trois mois. Qualité : toute qualité
  déclarée autre que `quelconque` (en pratique `interetAAgir`) [D-ED-37 — 30/09/2026].
  Les conditions préalables (mise en demeure, délai, exigence sur les
  griefs) sont dans PR-49 (`injonctionRecevable`) : `saisineRecevable` seul
  ne suffit pas pour cette voie.

  LIMITE DÉCLARÉE D-ED-36 (30/09/2026)
  ------------------------------------
  Le modèle SUPPOSE le tiers extérieur neutre. Barraud de Lagerie (Politix,
  2024, p. 131, 136) montre que cette neutralité se dispute aussi : juges
  consulaires, « professionnel·les du monde de l'entreprise » ; amici curiae
  mis en cause pour leurs liens avec les entreprises. La règle « un tiers lié
  ne tranche pas » (PR-41) n'est pas étendue aux tiers extérieurs
  `[LIMITE DÉCLARÉE]`.

  AJOUT D-ED-30 (30/09/2026, décision du porteur)
  -----------------------------------------------
  Voie `autoriteSupervision` : l'autorité de supervision de la directive
  (UE) 2024/1760, saisie par « des rapports étayés faisant état de
  préoccupations » (art. 26 §1, texte consolidé au 18/03/2026), qu'elle
  évalue et dont elle motive le résultat (art. 26 §4-5), avec recours
  (§6) ; elle peut enquêter (art. 25 §2). Voie publique : ouverte à
  « les personnes physiques et morales », sans le consentement de la
  société `[TRANSPOSITION DÉCLARÉE — la directive vise des sociétés, non
  des registres de communalité]`.

  AJOUT D-ED-29 (30/09/2026, décision du porteur)
  -----------------------------------------------
  Voie `arbitrage`, distincte de la `transaction` : l'arbitrage TRANCHE
  (sentence obligatoire, y compris contre une partie), la transaction
  ACCORDE (art. 2044 : « concessions réciproques », contrat écrit). Les deux
  sont privées et exigent le consentement de X ; mais le consentement à
  l'arbitrage peut être donné D'AVANCE (convention d'arbitrage, Accord
  Bangladesh 2013 §5), non celui d'une transaction, qui se donne sur
  l'issue (PR-46).

  CE QUE LE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne dit pas si une pollution est avérée, ni si un seuil est franchi :
    c'est le contenu des pièces, non leur statut.
  · Il ne modélise ni délais, ni prescription, ni recours, ni l'articulation
    entre voies (cumul, suspension).
  · La qualité à agir est une donnée déclarée, non vérifiée.
  · Ce n'est pas un conseil juridique.
-/

import ProfReg.PR43_InstanceDeControle

namespace ProfRegPR44

open ProfRegPR35 (Entite Ligne Registre)
open ProfRegPR43 (DesignationControle designe instanceCommune arbitrerInstitue)
open ProfRegPR40 (StatutEcart)
open ProfRegPR41 (StatutArbitre)

/-! ## 1. Point 1 — l'attestation interne -/

/-- Les pièces qui fondent une attestation. -/
inductive Piece where
  | mesureInterne        -- relevé, prélèvement, analyse faits par la communauté
  | constatCommissaire   -- constat d'un commissaire de justice (ord. 2016-728, art. 1)
  | rapportExpert        -- expertise (laboratoire, hydrologue)
  deriving DecidableEq, Repr

/-- La force d'une pièce devant un tiers. -/
inductive Force where
  | renseignement            -- à apprécier, sans valeur probante propre
  | libreAppreciation        -- admissible, appréciée par le tiers (art. 1358)
  | foiJusquaPreuveContraire -- présumée exacte, sauf preuve contraire
  deriving DecidableEq, Repr

/-- L'attestation interne, par l'instance de contrôle du registre. -/
structure Attestation where
  instanceCtrl : Entite
  pieces       : List Piece
  deriving DecidableEq, Repr

/-- L'attestation est valide : l'instance est désignée (arrêtée) par le
    registre `reg`, et n'est ni le teneur, ni l'entreprise visée `x`. -/
def attestationValide (ds : List DesignationControle) (reg x : Entite)
    (a : Attestation) : Bool :=
  designe ds reg a.instanceCtrl && !(a.instanceCtrl == reg) && !(a.instanceCtrl == x)

/-! ## 2. Point 2 — le tiers extérieur -/

inductive Voie where
  | negociation            -- droit privé : discussion avec X
  | transaction            -- droit privé : art. 2044 C. civ., écrit, concessions réciproques
  | arbitrage              -- droit privé : sentence obligatoire, sur convention d'arbitrage (D-ED-29)
  | jugeJudiciaire         -- droit public/civil : action en réparation du préjudice écologique
  | autoriteAdministrative -- police de l'eau : contrôle, mise en demeure (L.171-8)
  | parquet                -- plainte / dénonciation (art. 40 CPP) ; délit L.216-6
  | autoriteSupervision    -- CS3D art. 26 : rapport étayé ; art. 25 : enquête (D-ED-30)
  | injonctionVigilance    -- C. com. L.225-102-4 II ; préalables : PR-49 (D-ED-35)
  deriving DecidableEq, Repr

/-- La voie est-elle ouverte sans le consentement de X ? -/
def sansConsentement : Voie → Bool
  | .negociation => false
  | .transaction => false
  | .arbitrage   => false
  | _            => true

/-- La voie est-elle pénale ? (règle 3) -/
def penale : Voie → Bool
  | .parquet => true
  | _        => false

/-- La qualité du porteur de la saisine. -/
inductive Qualite where
  | quelconque
  | qualiteArt1248   -- personne « ayant qualité et intérêt à agir » (art. 1248)
  | interetAAgir     -- « toute personne justifiant d'un intérêt à agir » (L.225-102-4 II) (D-ED-35)
  deriving DecidableEq, Repr

structure Saisine where
  voie     : Voie
  qualite  : Qualite
  /-- X a-t-il accepté d'entrer dans la voie ? -/
  consentX : Bool
  /-- `none` : en cours ; `some true` : retenu ; `some false` : écarté. -/
  issue    : Option Bool
  deriving DecidableEq, Repr

/-- La saisine est recevable (règle 4). -/
def saisineRecevable (s : Saisine) : Bool :=
  match s.voie with
  | .negociation | .transaction | .arbitrage => s.consentX
  | .jugeJudiciaire             => decide (s.qualite = .qualiteArt1248)
  | .autoriteAdministrative | .parquet | .autoriteSupervision => true
  | .injonctionVigilance        => !(decide (s.qualite = .quelconque))

/-- La force d'une pièce, selon la voie (règles 2 et 3). -/
def force (v : Voie) : Piece → Force
  | .constatCommissaire => if penale v then .renseignement else .foiJusquaPreuveContraire
  | .mesureInterne      => if penale v then .renseignement else .libreAppreciation
  | .rapportExpert      => if penale v then .renseignement else .libreAppreciation

/-- L'attestation fait-elle foi (au moins une pièce qui fait foi) ? -/
def faitFoi (v : Voie) (a : Attestation) : Bool :=
  a.pieces.any (fun p => decide (force v p = .foiJusquaPreuveContraire))

/-! ## 3. Le statut du constat -/

inductive StatutConstat where
  | unilateral                        -- inscrit, refusé par X (PR-40 `refuse`)
  | atteste                           -- point 1
  | porte   (v : Voie)                -- point 2, en cours
  | tranche (v : Voie) (retenu : Bool)
  deriving DecidableEq, Repr

def statutConstat (ds : List DesignationControle) (reg x : Entite)
    (att : Option Attestation) (sais : Option Saisine) : StatutConstat :=
  match att with
  | none   => .unilateral
  | some a =>
    if attestationValide ds reg x a then
      match sais with
      | none   => .atteste
      | some s =>
        if saisineRecevable s then
          match s.issue with
          | none   => .porte s.voie
          | some b => .tranche s.voie b
        else .atteste
    else .unilateral

/-- La ligne suivie : la ligne du registre, et son statut. -/
structure LigneSuivie where
  ligne  : Ligne Nat
  statut : StatutConstat
  deriving DecidableEq, Repr

def suivre (ds : List DesignationControle) (reg x : Entite) (l : Ligne Nat)
    (att : Option Attestation) (sais : Option Saisine) : LigneSuivie :=
  ⟨l, statutConstat ds reg x att sais⟩

/-! ## 4. Ce qui se démontre (général) -/

/-- **Rien n'est effacé** : quel que soit le parcours, la ligne reste la même. -/
theorem le_parcours_n_efface_rien (ds : List DesignationControle) (reg x : Entite)
    (l : Ligne Nat) (att : Option Attestation) (sais : Option Saisine) :
    (suivre ds reg x l att sais).ligne = l := rfl

/-- **Sans attestation, rien n'est porté** au nom du registre (règle 6). -/
theorem sans_attestation_rien_n_est_porte (ds : List DesignationControle) (reg x : Entite)
    (sais : Option Saisine) : statutConstat ds reg x none sais = .unilateral := rfl

/-- **Sans le consentement de X, les voies privées sont fermées.** -/
theorem sans_consentement_la_voie_privee_est_fermee (q : Qualite) (i : Option Bool) :
    saisineRecevable ⟨.negociation, q, false, i⟩ = false
    ∧ saisineRecevable ⟨.transaction, q, false, i⟩ = false := ⟨rfl, rfl⟩

/-- **Les voies publiques ne dépendent pas du consentement de X.** -/
theorem la_voie_publique_ignore_le_refus (v : Voie) (q : Qualite) (i : Option Bool)
    (h : sansConsentement v = true) :
    saisineRecevable ⟨v, q, false, i⟩ = saisineRecevable ⟨v, q, true, i⟩ := by
  cases v <;> first | rfl | (simp [sansConsentement] at h)

/-- **Sans pièce extérieure, pas de foi** : un dossier fait de mesures
    internes (même attesté) n'est jamais « foi jusqu'à preuve contraire »
    (art. 1363). -/
theorem sans_piece_exterieure_pas_de_foi (v : Voie) (i : Entite) (n : Nat) :
    faitFoi v ⟨i, List.replicate n .mesureInterne⟩ = false := by
  unfold faitFoi
  induction n with
  | zero => rfl
  | succ k ih =>
    show (decide (force v .mesureInterne = .foiJusquaPreuveContraire)
          || (List.replicate k Piece.mesureInterne).any _) = false
    rw [ih, Bool.or_false]
    cases v <;> rfl

/-- **D-ED-29 — l'arbitrage est une voie privée** : sans convention
    d'arbitrage (consentement de X), il est fermé ; avec, il est ouvert,
    et la pièce extérieure y fait foi (voie civile). -/
theorem l_arbitrage_exige_une_convention (q : Qualite) (i : Option Bool) :
    saisineRecevable ⟨.arbitrage, q, false, i⟩ = false
    ∧ saisineRecevable ⟨.arbitrage, q, true, i⟩ = true
    ∧ force .arbitrage .constatCommissaire = .foiJusquaPreuveContraire := ⟨rfl, rfl, rfl⟩

/-- **D-ED-30 — l'autorité de supervision est une voie publique** : le
    refus de la société ne la ferme pas ; aucune qualité particulière n'est
    exigée (« les personnes physiques et morales », art. 26 §1). -/
theorem l_autorite_de_supervision_ne_depend_pas_de_la_societe (q : Qualite) (i : Option Bool) :
    saisineRecevable ⟨.autoriteSupervision, q, false, i⟩ = true
    ∧ sansConsentement .autoriteSupervision = true := ⟨rfl, rfl⟩

/-- **Au pénal, même le constat d'un commissaire n'est que renseignement.** -/
theorem au_penal_le_constat_renseigne :
    force .parquet .constatCommissaire = .renseignement
    ∧ force .jugeJudiciaire .constatCommissaire = .foiJusquaPreuveContraire := ⟨rfl, rfl⟩

/-! ## 5. Instance : la rivière et l'entreprise X -/

def riviere        : Entite := 10
def entrepriseX    : Entite := 2
def comiteDuFleuve : Entite := 70
def associationAgreee : Entite := 80   -- porteur ayant qualité (art. 1248), déclaré

/-- La rivière désigne son instance ; X ne désigne rien. -/
def dsRiviere : List DesignationControle := [⟨riviere, comiteDuFleuve, .arretee⟩]

/-- La ligne du registre de la rivière envers X : prélèvement de 120 (m³/j,
    par exemple), sans miroir. -/
def ligneX : Ligne Nat := ⟨entrepriseX, .Cplus, 120⟩
def regRiviere : Registre Nat := ⟨riviere, [ligneX]⟩

def attMesures : Attestation := ⟨comiteDuFleuve, [.mesureInterne, .rapportExpert]⟩
def attAvecConstat : Attestation :=
  ⟨comiteDuFleuve, [.mesureInterne, .rapportExpert, .constatCommissaire]⟩
/-- X qui s'attesterait lui-même : irrecevable. -/
def attParX : Attestation := ⟨entrepriseX, [.mesureInterne]⟩

/-- **PR-44 (1) — l'attestation interne ne tranche pas envers X.** Le comité
    atteste ; mais X ne l'a pas désigné : aucun arbitrage interne (PR-43). -/
theorem l_attestation_interne_ne_tranche_pas :
    statutConstat dsRiviere riviere entrepriseX (some attMesures) none = .atteste
    ∧ arbitrerInstitue dsRiviere .refuse (some ⟨comiteDuFleuve, false, .confirme⟩)
        entrepriseX riviere = .nonArbitre .refuse := by
  decide

/-- **PR-44 (2) — le refus de X ferme la négociation, pas le préfet.** -/
theorem le_refus_ne_ferme_que_la_voie_privee :
    statutConstat dsRiviere riviere entrepriseX (some attMesures)
        (some ⟨.negociation, .quelconque, false, none⟩) = .atteste
    ∧ statutConstat dsRiviere riviere entrepriseX (some attMesures)
        (some ⟨.autoriteAdministrative, .quelconque, false, none⟩)
        = .porte .autoriteAdministrative := by
  decide

/-- **PR-44 (3) — devant le juge du préjudice écologique, la qualité
    compte** : le comité seul (qualité non déclarée) n'est pas recevable ;
    porté par une personne ayant qualité, il l'est. -/
theorem le_juge_exige_la_qualite :
    statutConstat dsRiviere riviere entrepriseX (some attAvecConstat)
        (some ⟨.jugeJudiciaire, .quelconque, false, none⟩) = .atteste
    ∧ statutConstat dsRiviere riviere entrepriseX (some attAvecConstat)
        (some ⟨.jugeJudiciaire, .qualiteArt1248, false, some true⟩)
        = .tranche .jugeJudiciaire true := by
  decide

/-- **PR-44 (4) — la transaction, si X y entre.** -/
theorem la_transaction_suppose_x :
    statutConstat dsRiviere riviere entrepriseX (some attAvecConstat)
        (some ⟨.transaction, .quelconque, true, some true⟩) = .tranche .transaction true := by
  decide

/-- **PR-44 (5) — le constat du commissaire change la force, pas le statut.** -/
theorem la_piece_exterieure_fait_foi_au_civil :
    faitFoi .jugeJudiciaire attMesures = false
    ∧ faitFoi .jugeJudiciaire attAvecConstat = true
    ∧ faitFoi .parquet attAvecConstat = false := by
  decide

/-- **Témoin discriminant** (R-7) de `statutConstat` : sur la même ligne,
    les quatre statuts sont atteints ; X ne s'atteste pas lui-même. -/
theorem statut_constat_temoin_discriminant :
    statutConstat dsRiviere riviere entrepriseX none none = .unilateral
    ∧ statutConstat dsRiviere riviere entrepriseX (some attParX) none = .unilateral
    ∧ statutConstat dsRiviere riviere entrepriseX (some attMesures) none = .atteste
    ∧ statutConstat dsRiviere riviere entrepriseX (some attMesures)
        (some ⟨.parquet, .quelconque, false, none⟩) = .porte .parquet
    ∧ statutConstat dsRiviere riviere entrepriseX (some attMesures)
        (some ⟨.autoriteAdministrative, .quelconque, false, some false⟩)
        = .tranche .autoriteAdministrative false := by
  decide

end ProfRegPR44
