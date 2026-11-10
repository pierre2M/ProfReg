import ProfReg.PR58_CommunTroisInstances

/-
  PR-59 · Écart formel / réel droit par droit ; inclusivité instance par instance
  (NT-G6 §2.1, §3.1, §3.2 ; NT-ARCH F6, C-DROITS)
  ===============================================================================

  Décisions du porteur (13/10/2026, fichier d'état §2, n° 54 et 55).

  · **Écart par droit.** `ecart_formel_réel` se déclare pour chacun des cinq
    droits de Schlager & Ostrom (1992) — accès, prélèvement (niveau
    opérationnel, p. 250), gestion, exclusion, aliénation (niveau du choix
    collectif, p. 251) —, chacun avec son seuil déclaré et son porteur. Alerte
    si l'écart atteint le seuil sur deux cycles ; sans seuil déclaré, marqueur ;
    écart non instruit ≠ écart nul ; aucun score global ; un commun sans
    faisceau (intérêt diffus) n'a pas d'écart mesurable.
  · **Inclusivité par instance.** `communalite_inclusivite` se déclare pour
    chacune des trois instances (attributaire, délibérative, contrôle) —
    Rochfeld, Cornu & Martin 2021. Le **second sens** de la séparabilité des
    axes (l'inclusivité ne détermine pas l'intérêt commun) est établi **sur
    l'instance de contrôle** : l'action populaire, « totalement ouverte à
    quiconque », défend un intérêt commun (p. 411) ; le recours pour excès de
    pouvoir, « très largement ouvert », défend l'intérêt général, qui « rend
    invisible la communauté » (p. 332-333). Le premier sens (PR-58) se lit sur
    l'instance attributaire.

  Ce fichier établit la forme de ces règles, non la valeur d'un écart ni la
  qualification juridique d'une figure. `[RÉSERVE DE MODÈLE]` Écarts et seuils
  codés par des entiers ; l'instance délibérative n'a aucun témoin (ni pour un
  sens ni pour l'autre). Lean 4 pur, sans Mathlib ; importe PR-58.

  Porteur : Pierre Musseau. Écrit le 13 octobre 2026.
-/

namespace ProfRegPR59

open ProfRegPR58

/-! ## 1. L'écart droit par droit -/

/-- Les cinq droits (Schlager & Ostrom 1992, p. 250-251). -/
inductive Droit where
  | acces | prelevement | gestion | exclusion | alienation
  deriving DecidableEq, Repr

/-- Le niveau du droit : opérationnel (usage) ou choix collectif (pouvoir). -/
def choixCollectif : Droit → Bool
  | .acces => false
  | .prelevement => false
  | _ => true

/-- L'écart d'un droit sur deux cycles, et son seuil déclaré. `none` : non
    instruit (écart) ou non déclaré (seuil). -/
structure EcartDroit where
  cycle1 : Option Nat
  cycle2 : Option Nat
  seuil : Option Nat
  deriving DecidableEq, Repr

def depasse (x : Option Nat) (s : Nat) : Bool :=
  match x with
  | some v => decide (s ≤ v)
  | none => false

/-- **Alerte** sur un droit : l'écart atteint le seuil déclaré sur deux cycles. -/
def alerte (e : EcartDroit) : Bool :=
  match e.seuil with
  | some s => depasse e.cycle1 s && depasse e.cycle2 s
  | none => false

def marqueurSeuilNonDeclare (e : EcartDroit) : Bool := e.seuil.isNone

def marqueurNonInstruit (e : EcartDroit) : Bool := e.cycle1.isNone || e.cycle2.isNone

/-- Le profil d'un commun : un écart par droit, ou aucun faisceau. -/
structure Profil where
  sansFaisceau : Bool
  ecart : Droit → EcartDroit

def alerteDroit (p : Profil) (d : Droit) : Bool := !p.sansFaisceau && alerte (p.ecart d)

/-- **PR-59 (1) — pas d'alerte sans seuil déclaré pour ce droit.** -/
theorem pas_d_alerte_sans_seuil_declare (e : EcartDroit) (h : e.seuil = none) :
    alerte e = false ∧ marqueurSeuilNonDeclare e = true := by
  simp [alerte, marqueurSeuilNonDeclare, h]

/-- **PR-59 (2) — un écart non instruit n'est pas un écart nul** : il ne
    lève pas d'alerte et il est marqué ; un écart nul instruit ne l'est pas. -/
theorem non_instruit_n_est_pas_nul :
    let e₀ : EcartDroit := ⟨some 0, some 0, some 1⟩
    let e? : EcartDroit := ⟨none, some 0, some 1⟩
    alerte e? = false ∧ marqueurNonInstruit e? = true ∧ marqueurNonInstruit e₀ = false := ⟨rfl, rfl, rfl⟩

/-- **PR-59 (3) — un seul cycle au-dessus du seuil ne suffit pas.** -/
theorem un_cycle_ne_suffit_pas :
    alerte ⟨some 5, some 0, some 3⟩ = false ∧ alerte ⟨some 5, some 4, some 3⟩ = true := ⟨rfl, rfl⟩

/-- Deux jardins partagés : même écart total, droits différents. -/
def jardinPouvoir : Profil :=
  ⟨false, fun d => if d == .gestion then ⟨some 4, some 4, some 3⟩ else ⟨some 0, some 0, some 3⟩⟩

def jardinUsage : Profil :=
  ⟨false, fun d => if d == .acces then ⟨some 4, some 4, some 3⟩ else ⟨some 0, some 0, some 3⟩⟩

/-- **PR-59 (4) — les alertes par droit sont indépendantes, et un même écart
    total ne dit pas quel droit dérive.** Le premier jardin alerte sur la
    gestion (choix collectif : un problème de pouvoir), le second sur l'accès
    (niveau opérationnel : un problème d'usage). -/
theorem meme_ecart_total_droits_differents :
    alerteDroit jardinPouvoir .gestion = true ∧ alerteDroit jardinPouvoir .acces = false
  ∧ alerteDroit jardinUsage .acces = true ∧ alerteDroit jardinUsage .gestion = false
  ∧ choixCollectif .gestion = true ∧ choixCollectif .acces = false := by
  decide

/-- **PR-59 (5) — un commun sans faisceau n'a pas d'écart mesurable** : aucun
    droit n'y lève d'alerte, quels que soient les écarts saisis. -/
theorem sans_faisceau_pas_d_alerte (p : Profil) (h : p.sansFaisceau = true) (d : Droit) :
    alerteDroit p d = false := by
  simp [alerteDroit, h]

/-! ## 2. L'inclusivité instance par instance et le second sens -/

/-- Les axes déclarés, l'inclusivité par instance (`none` : non déclarée). -/
structure AxesParInstance where
  interetCommun : Bool
  inclAttributaire : Option Inclusivite
  inclDeliberative : Option Inclusivite
  inclControle : Option Inclusivite
  deriving DecidableEq, Repr

/-- L'action populaire : « totalement ouverte à quiconque », en défense d'un
    intérêt commun diffus (rapport, p. 411). -/
def actionPopulaire : AxesParInstance := ⟨true, none, none, some .forte⟩

/-- Le recours pour excès de pouvoir : « très largement ouvert », en défense
    de l'intérêt général, qui n'est pas un intérêt commun (p. 332-333). -/
def recoursInteretGeneral : AxesParInstance := ⟨false, none, none, some .forte⟩

/-- L'action de groupe : ouverte aux personnes placées dans une situation
    similaire ; intérêts « divisibles et répartissables » (p. 332). -/
def actionDeGroupe : AxesParInstance := ⟨false, none, none, some .intermediaire⟩

/-- **PR-59 (6) — l'inclusivité de l'instance de contrôle ne détermine pas
    l'intérêt commun** (second sens, sur l'instance de contrôle). -/
theorem l_inclusivite_du_controle_ne_determine_pas_l_interet_commun :
    ¬ ∃ f : Option Inclusivite → Bool,
        f actionPopulaire.inclControle = actionPopulaire.interetCommun
      ∧ f recoursInteretGeneral.inclControle = recoursInteretGeneral.interetCommun := by
  rintro ⟨f, h1, h2⟩
  simp only [actionPopulaire, recoursInteretGeneral] at h1 h2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- **Témoin** : à intérêt commun absent, l'inclusivité du contrôle varie
    (recours pour excès de pouvoir, action de groupe). -/
theorem controle_temoin :
    recoursInteretGeneral.interetCommun = actionDeGroupe.interetCommun
  ∧ recoursInteretGeneral.inclControle ≠ actionDeGroupe.inclControle := by
  decide

/-- La communauté fermée et la chose commune, déclarées sur l'instance
    attributaire. -/
def communauteFermeeI : AxesParInstance := ⟨true, some .faible, none, none⟩
def choseCommuneI : AxesParInstance := ⟨true, some .forte, none, none⟩

/-- **PR-59 (7) — le premier sens se lit sur l'instance attributaire** :
    l'intérêt commun ne détermine pas l'inclusivité attributaire (forme par
    instance de `l_interet_commun_ne_determine_pas_l_inclusivite`, PR-58). -/
theorem le_premier_sens_porte_sur_l_attributaire :
    ¬ ∃ f : Bool → Option Inclusivite,
        f communauteFermeeI.interetCommun = communauteFermeeI.inclAttributaire
      ∧ f choseCommuneI.interetCommun = choseCommuneI.inclAttributaire := by
  rintro ⟨f, h1, h2⟩
  simp only [communauteFermeeI, choseCommuneI] at h1 h2
  rw [h1] at h2
  simp at h2

end ProfRegPR59
