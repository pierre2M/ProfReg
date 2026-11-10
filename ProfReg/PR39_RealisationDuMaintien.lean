/-
  PR-39 · La réalisation du maintien : attendu, constaté, contesté
  ===============================================================

  Porteur : Pierre Musseau. Écrit le 30 septembre 2026, sur décision D-ED-15.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR35_EcritureDuale` et
  `ProfReg.PR23_MouvementDeMaintien`.

  LE PROBLÈME (note du 30/09, point γ)
  ------------------------------------
  PR-23 et PR-37 vérifient qu'un maintien est INSCRIT, et PR-23 §6 calcule la
  dette de préservation (dû − engagé). Rien ne dit si le RÉSULTAT a été
  atteint. Le journal MRC de LFDE 2025 le montre sur le terrain : il inscrit
  des écritures `e → d` dont le `d` est « un résultat attendu pour le
  collectif bénéficiaire », et précise « Il ne faut pas lire ce crédit
  comme […] la preuve que le résultat a été atteint » ; ce `d` est écrit par
  LFDE elle-même.

  LA RÉPONSE (D-ED-15)
  --------------------
  La réalisation est elle-même une ÉCRITURE DUALE : A inscrit l'effort
  engagé ; le résultat n'est CONSTATÉ que s'il est inscrit par L'AUTRE
  teneur (le titulaire du registre du milieu ou du collectif, par son
  écrivant). Trois états : `attendu` (aucun constat de B), `constate`
  (B constate le résultat), `conteste` (B constate qu'il n'est pas atteint).
  Un constat écrit par A lui-même ne compte pas.

  Ce qui n'est pas constaté NE DÉCHARGE RIEN : tout le dû reste ouvert. Ce qui
  est constaté ramène l'obligation à la dette de préservation (dû − engagé,
  PR-23 §6). Et une obligation non reconduite à l'exercice suivant revient
  à l'état `attendu` — contre la « perte de bouclage » (Vuattoux, chap. 2 :
  un dispositif peut produire des effets pendant deux ans « puis se défaire
  en quelques mois »).

  CE QUE LE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne dit pas COMMENT B constate : le critère de vérification est celui
    que porte le maintien (`critere`, CONV-11) ; il n'est pas évalué ici.
  · Il ne tranche pas un constat contesté : `conteste` est un état inscrit,
    non une décision (voir PR-40 et D-ED-12 pour l'arbitrage par un tiers).
-/

import ProfReg.PR35_EcritureDuale
import ProfReg.PR23_MouvementDeMaintien

namespace ProfRegPR39

open ProfRegPR35 (Entite)
open ProfRegPR23 (MaintienCONV11 Situation)

/-! ## 1. Le constat et l'état du résultat -/

inductive EtatResultat where
  | attendu    -- aucun constat de l'autre teneur
  | constate   -- l'autre teneur constate que le résultat est atteint
  | conteste   -- l'autre teneur constate qu'il ne l'est pas
  deriving DecidableEq, Repr

/-- Un constat : qui l'inscrit, et ce qu'il constate. -/
structure Constat where
  parTeneur : Entite
  atteint   : Bool
  deriving DecidableEq, Repr

/-- Une ligne de réalisation, pour un exercice : le maintien (six éléments de
    CONV-11, dû et engagé) et, le cas échéant, un constat. -/
structure LigneRealisation where
  exercice : Nat
  maintien : MaintienCONV11 Entite Entite Nat
  constat  : Option Constat

/-- **L'état du résultat, lu depuis l'autre teneur `b`.** Un constat écrit
    par un autre que `b` — en particulier par celui qui a fait l'effort — ne
    compte pas. -/
def etat (l : LigneRealisation) (b : Entite) : EtatResultat :=
  match l.constat with
  | none   => .attendu
  | some c =>
    if c.parTeneur == b then (if c.atteint then .constate else .conteste)
    else .attendu

/-- **Ce qui reste ouvert.** Non constaté : tout le dû. Constaté : la dette
    de préservation (dû − engagé), calculée par PR-23 §6. -/
def resteOuvert (l : LigneRealisation) (b : Entite) : Nat :=
  match etat l b with
  | .constate => l.maintien.solde
  | _         => l.maintien.situation.du

/-! ## 2. Ce qui se démontre -/

/-- **Sans constat, rien n'est déchargé** : tout le dû reste ouvert, quel que
    soit ce qui a été engagé. -/
theorem sans_constat_rien_n_est_decharge (l : LigneRealisation) (b : Entite)
    (h : etat l b ≠ .constate) : resteOuvert l b = l.maintien.situation.du := by
  unfold resteOuvert
  cases he : etat l b <;> simp_all

/-- **Le constat ramène l'obligation à la dette de préservation.** -/
theorem le_constat_ramene_a_la_dette_de_preservation (l : LigneRealisation) (b : Entite)
    (h : etat l b = .constate) : resteOuvert l b = l.maintien.solde := by
  unfold resteOuvert; rw [h]

/-! ## 3. Instance : l'entreprise et la rivière, puis LFDE -/

def entreprise : Entite := 2
def riviere    : Entite := 10
def collectifRiverain : Entite := 13

def maintienR : MaintienCONV11 Entite Entite Nat :=
  ⟨collectifRiverain, entreprise, riviere, ⟨100, 60⟩, 2030, 1⟩

/-- L'effort seul : aucun constat. -/
def effortSeul : LigneRealisation := ⟨2026, maintienR, none⟩
/-- Le constat inscrit par le collectif riverain (écrivant du registre de la
    rivière) : résultat atteint. -/
def constatRiverain : LigneRealisation := ⟨2026, maintienR, some ⟨riviere, true⟩⟩
/-- Le « constat » inscrit par l'entreprise elle-même. -/
def autoConstat : LigneRealisation := ⟨2026, maintienR, some ⟨entreprise, true⟩⟩
/-- Le collectif constate que le résultat n'est pas atteint. -/
def constatNegatif : LigneRealisation := ⟨2026, maintienR, some ⟨riviere, false⟩⟩

/-- **PR-39 (1) — attendu n'est pas constaté.** Même maintien, même effort :
    sans constat, 100 restent ouverts ; constaté par l'autre teneur, 40 (la
    dette de préservation). -/
theorem attendu_n_est_pas_constate :
    etat effortSeul riviere = .attendu ∧ resteOuvert effortSeul riviere = 100
    ∧ etat constatRiverain riviere = .constate ∧ resteOuvert constatRiverain riviere = 40 := by
  decide

/-- **PR-39 (2) — l'auto-constat ne vaut pas.** Un constat inscrit par celui
    qui a fait l'effort laisse le résultat `attendu` : c'est le cas du
    journal LFDE 2025, où le `d` est écrit par LFDE. -/
theorem l_auto_constat_ne_vaut_pas :
    etat autoConstat riviere = .attendu ∧ resteOuvert autoConstat riviere = 100 := by
  decide

/-- **PR-39 (3) — la contestation est inscrite, non effacée.** -/
theorem la_contestation_est_inscrite :
    etat constatNegatif riviere = .conteste ∧ resteOuvert constatNegatif riviere = 100 := by
  decide

/-! ## 4. La reconduction — contre la perte de bouclage -/

/-- L'état d'une obligation pour un exercice donné, lu dans la suite des
    lignes de réalisation : sans ligne pour cet exercice, `attendu`. -/
def etatExercice (ls : List LigneRealisation) (n : Nat) (b : Entite) : EtatResultat :=
  match ls.find? (fun l => l.exercice == n) with
  | some l => etat l b
  | none   => .attendu

/-- **PR-39 (4) — ce qui n'est pas reconduit revient en attente.** Constaté
    en 2026, l'état de 2027 est `attendu` si aucune ligne n'est inscrite pour
    2027 : un constat ne vaut que pour son exercice. -/
theorem non_reconduit_revient_en_attente :
    etatExercice [constatRiverain] 2026 riviere = .constate
    ∧ etatExercice [constatRiverain] 2027 riviere = .attendu := by
  decide

/-- **Témoin discriminant** (R-7) de `etat` : les trois valeurs sont
    atteintes. -/
theorem etat_temoin_discriminant :
    etat effortSeul riviere = .attendu
    ∧ etat constatRiverain riviere = .constate
    ∧ etat constatNegatif riviere = .conteste := by
  decide

end ProfRegPR39
