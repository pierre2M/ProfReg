/-
  PR-58 · Un commun suppose ses instances ; les axes se déclarent séparément
  (NT-ARCH §8.5.6.3, §8.5.6.4, §8.5.6.2bis ; NT-G6 §2.1)
  ==========================================================================

  Décision du porteur (13/10/2026, fichier d'état §2, n° 52).

  · **NT-ARCH §8.5.6.4.** Le typage T (`P+ + D+ ↔ C+`) établit l'instance
    attributaire, « et elle seule » : il est **nécessaire et non suffisant**.
    « Toute inscription d'une chose comme commun déclare […]
    `communalite_instance` incluant DELIBERATIVE et CONTROLE, et nomme leurs
    porteurs. » Une chose dont les utilités sont distribuées sans que personne
    ne fixe collectivement les règles « n'est pas un commun : c'est une
    indivision, une servitude, ou une fiducie ».
  · **§8.5.6.3.** Trois configurations de communalité (chose commune de
    l'art. 714 ; propriété collective avec règles d'usage `P+ + D+ ↔ C+` ;
    intérêt diffus `E+ ↔ ∅`) et une configuration négative (`P+` seul : chose
    sans maître occupée, propriété exclusive).
  · **§8.5.6.2bis.** Une forme admise (fiducie, ORE, ORIC) qui satisfait la
    condition T sans instance délibérative déclarée « n'est pas inscrite comme
    commun » — illustration : le marais des Lagneux (rapport, p. 308).
  · **NT-G6 §2.1, condition de réfutation.** « Cette grammaire tombe si l'on
    montre que les axes de la communalité juridique ne sont pas déclarables
    séparément. » Témoin tiré de la source : la communauté fermée (Rochfeld,
    Cornu & Martin 2021, p. 336-337), intérêt commun présent, inclusivité
    faible ; et la chose commune de l'art. 714, intérêt commun présent, usage
    « commun à tous ».

  Ce fichier établit la **forme** de ces règles, jamais qu'une chose est un
  commun. `[RÉSERVE DE MODÈLE]` Le typage est réduit à ses patrons ; les
  porteurs sont codés par des entiers ; l'inclusivité par trois niveaux
  déclarés. La séparabilité n'est établie que dans un sens (l'intérêt commun
  ne fixe pas l'inclusivité). Lean 4 pur, sans Mathlib, sans import.

  Porteur : Pierre Musseau. Écrit le 13 octobre 2026.
-/

namespace ProfRegPR58

/-! ## 1. Le modèle -/

/-- Les patrons d'écriture d'une chose (§8.5.6.2, §8.5.6.3). -/
inductive Patron where
  /-- `P+ + D+ ↔ C+` : propriété collective avec règles d'usage, ou forme admise. -/
  | detentionObligee
  /-- `E+ ↔ ∅` qualifiant : intérêt diffus. -/
  | interetDiffus
  /-- Usage universel sans `P` : chose commune (art. 714). -/
  | choseCommune
  /-- `P+` seul : propriété exclusive, ou chose sans maître occupée. -/
  | proprieteSeule
  deriving DecidableEq, Repr

/-- La condition T : l'écriture porte l'un des trois patrons de communalité. -/
def conditionT : Patron → Bool
  | .proprieteSeule => false
  | _ => true

/-- `porteur_instance` (C-DROITS, F6) : qui tient chaque instance. -/
structure Instances where
  attributaire : Option Nat
  deliberative : Option Nat
  controle : Option Nat
  deriving DecidableEq, Repr

structure Chose where
  patron : Patron
  instances : Instances
  deriving DecidableEq, Repr

/-- **Inscrite comme commun** (§8.5.6.2 et §8.5.6.4). -/
def inscriteCommeCommun (c : Chose) : Bool :=
  conditionT c.patron && c.instances.deliberative.isSome && c.instances.controle.isSome

/-! ## 2. Le typage est nécessaire, non suffisant -/

/-- **PR-58 (1) — le typage est nécessaire.** -/
theorem le_typage_est_necessaire (c : Chose) (h : inscriteCommeCommun c = true) :
    conditionT c.patron = true := by
  simp only [inscriteCommeCommun, Bool.and_eq_true] at h
  exact h.1.1

/-- **PR-58 (2) — sans instance délibérative, pas de commun**, quel que soit
    le typage. -/
theorem sans_instance_deliberative_pas_de_commun (c : Chose)
    (h : c.instances.deliberative = none) : inscriteCommeCommun c = false := by
  simp [inscriteCommeCommun, h]

/-- **PR-58 (3) — sans instance de contrôle, pas de commun.** -/
theorem sans_instance_de_controle_pas_de_commun (c : Chose)
    (h : c.instances.controle = none) : inscriteCommeCommun c = false := by
  simp [inscriteCommeCommun, h]

/-- **PR-58 (4) — le typage ne suffit pas : une indivision n'est pas un
    commun.** Utilités distribuées (`P+ + D+ ↔ C+`, attributaire tenu), aucune
    instance délibérative ni de contrôle. -/
theorem une_indivision_n_est_pas_un_commun :
    conditionT .detentionObligee = true
  ∧ inscriteCommeCommun ⟨.detentionObligee, ⟨some 1, none, none⟩⟩ = false := ⟨rfl, rfl⟩

/-- **PR-58 (5) — le marais des Lagneux.** Une ORE (forme admise) satisfait
    la condition T ; sans instance délibérative déclarée, la chose n'est pas
    inscrite comme commun (§8.5.6.2bis). -/
theorem une_forme_admise_sans_deliberation_n_est_pas_un_commun :
    inscriteCommeCommun ⟨.detentionObligee, ⟨none, none, some 2⟩⟩ = false := rfl

/-- **PR-58 (6) — `P+` seul n'est jamais un commun**, quelles que soient les
    instances déclarées (configuration négative, §8.5.6.3). -/
theorem la_propriete_seule_n_est_jamais_un_commun (i : Instances) :
    inscriteCommeCommun ⟨.proprieteSeule, i⟩ = false := by
  simp [inscriteCommeCommun, conditionT]

/-- **PR-58 (7) — l'intérêt diffus se passe d'attributaire.** Une chose
    `E+ ↔ ∅`, sans acteur attributaire identifié, est inscrite comme commun si
    ses instances délibérative et de contrôle sont tenues (§8.5.6.3, troisième
    configuration). -/
theorem l_interet_diffus_se_passe_d_attributaire :
    inscriteCommeCommun ⟨.interetDiffus, ⟨none, some 1, some 2⟩⟩ = true := rfl

/-- **Témoin discriminant** : la même propriété collective avec règles
    d'usage est un commun avec ses trois instances, non sans instance de
    contrôle. -/
theorem commun_temoin_discriminant :
    inscriteCommeCommun ⟨.detentionObligee, ⟨some 1, some 2, some 3⟩⟩ = true
  ∧ inscriteCommeCommun ⟨.detentionObligee, ⟨some 1, some 2, none⟩⟩ = false := ⟨rfl, rfl⟩

/-! ## 3. Les axes se déclarent séparément (NT-G6 §2.1) -/

inductive Inclusivite where
  | faible | intermediaire | forte
  deriving DecidableEq, Repr

/-- Une qualification déclarée sur deux axes (`communalite_interet_commun`,
    `communalite_inclusivite`), réduite à leur valeur. -/
structure Axes where
  interetCommun : Bool
  inclusivite : Inclusivite
  deriving DecidableEq, Repr

/-- La communauté fermée (rapport, p. 336-337) : intérêt commun présent,
    membres « strictement identifiés, voire sélectionnés ». -/
def communauteFermee : Axes := ⟨true, .faible⟩

/-- La chose commune (art. 714) : « l'usage est commun à tous ». -/
def choseCommuneArt714 : Axes := ⟨true, .forte⟩

/-- **PR-58 (8) — l'intérêt commun ne détermine pas l'inclusivité.** Aucune
    fonction de l'axe « intérêt commun » ne donne l'inclusivité des deux
    figures de la source : la condition de réfutation de NT-G6 §2.1 n'est pas
    réalisée par elles. `[LIMITE — un seul sens est établi.]` -/
theorem l_interet_commun_ne_determine_pas_l_inclusivite :
    ¬ ∃ f : Bool → Inclusivite,
        f communauteFermee.interetCommun = communauteFermee.inclusivite
      ∧ f choseCommuneArt714.interetCommun = choseCommuneArt714.inclusivite := by
  rintro ⟨f, h1, h2⟩
  simp only [communauteFermee, choseCommuneArt714] at h1 h2
  rw [h1] at h2
  exact Inclusivite.noConfusion h2

end ProfRegPR58
