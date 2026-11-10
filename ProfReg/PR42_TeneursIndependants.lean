/-
  PR-42 · Teneurs indépendants : quand une écriture duale fait preuve
  ==================================================================

  Porteur : Pierre Musseau. Écrit le 30 septembre 2026, sur décision D-ED-17.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR41_ArbitrageParUnTiers` et
  `ProfReg.PR38_ReciproquesIntragroupe`.

  LE PROBLÈME (note du 30/09, situations S2 et S5)
  ------------------------------------------------
  La condition de réfutation d'AX-15 exige « deux registres tenus
  indépendamment ». Sous contrôle commun (mère / filiale), le registre de la
  filiale peut être écrit sur instruction de la mère ; sous subordination
  (employeur / collectif d'employés), la contribution des travailleurs « ne
  supprime pas les rapports d'autorité internes à l'organisation »
  (Vuattoux, chap. 2). L'écriture duale y risque l'AUTO-CONFIRMATION
  `[RAISONNEMENT AUTORÉFÉRENTIEL — sous contrôle commun ou subordination]`.

  LES APPUIS
  ----------
  · ISA 505 §2 : « Audit evidence is more reliable when it is obtained from
    independent sources outside the entity ».
  · ISA 550 §10(a) : transaction « arm's length » — « as between a willing
    buyer and a willing seller who are unrelated and are acting
    independently of each other » ; §10(b) : est partie liée une entité
    « under common control with the reporting entity » ; §2 : les
    transactions entre parties liées « may not be conducted under normal
    market terms and conditions ».
  · Subordination : l'exécution d'un travail « sous l'autorité d'un employeur
    qui a le pouvoir de donner des ordres et des directives, d'en contrôler
    l'exécution et de sanctionner les manquements » (Cass. soc., 13 novembre
    1996, n° 94-13.187) `[VÉRIFIÉ sur reproductions secondaires — arrêt non
    lu]`.

  LA RÈGLE FORMALISÉE (D-ED-17)
  -----------------------------
  Une écriture duale FAIT PREUVE (sert d'appui) si :
    · les deux teneurs sont INDÉPENDANTS ; ou
    · ils sont sous contrôle commun ou en subordination, ET un TIERS
      RECEVABLE (PR-41 : ni l'un ni l'autre, non lié) a CONFIRMÉ.
  Sinon, elle reste inscrite — elle n'est ni refusée ni effacée — mais elle
  ne prouve rien à elle seule.

  CE QUE LE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne DÉTERMINE pas la relation entre teneurs : elle est déclarée.
    Une relation déclarée « indépendants » à tort n'est pas détectée.
  · Il ne dit pas que toute écriture duale entre parties liées est fausse :
    il dit qu'elle ne suffit pas à se prouver elle-même.
-/

import ProfReg.PR41_ArbitrageParUnTiers
import ProfReg.PR38_ReciproquesIntragroupe

namespace ProfRegPR42

open ProfRegPR35 (Entite Registre EcritureDuale)
open ProfRegPR41 (Investigation Issue tiersRecevable)

/-! ## 1. La relation entre teneurs, et la preuve -/

inductive Relation where
  | independants
  | controleCommun   -- ISA 550 §10(b)
  | subordination    -- employeur / collectif de salariés
  deriving DecidableEq, Repr

/-- Une confirmation par un tiers recevable. -/
def confirmeeParTiers (inv : Option Investigation) (a b : Entite) : Bool :=
  match inv with
  | some i => tiersRecevable i a b && decide (i.issue = .confirme)
  | none   => false

/-- **L'écriture duale fait preuve.** -/
def Probante {V : Type} (rel : Relation) (RA RB : Registre V)
    (inv : Option Investigation) : Prop :=
  EcritureDuale RA RB ∧
    (rel = .independants ∨ confirmeeParTiers inv RA.teneur RB.teneur = true)

instance {V : Type} [DecidableEq V] (rel : Relation) (RA RB : Registre V)
    (inv : Option Investigation) : Decidable (Probante rel RA RB inv) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## 2. Ce qui se démontre -/

/-- **Rien n'est probant sans écriture duale.** La preuve s'ajoute à
    l'écriture duale, elle ne la remplace pas. -/
theorem probante_suppose_la_duale {V : Type} (rel : Relation) (RA RB : Registre V)
    (inv : Option Investigation) (h : Probante rel RA RB inv) : EcritureDuale RA RB :=
  h.1

/-- **Entre teneurs liés, sans tiers, l'écriture duale ne prouve pas.** -/
theorem entre_lies_sans_tiers_rien_ne_prouve {V : Type} (RA RB : Registre V)
    (rel : Relation) (hrel : rel ≠ .independants) : ¬ Probante rel RA RB none := by
  rintro ⟨-, h | h⟩
  · exact hrel h
  · simp [confirmeeParTiers] at h

/-! ## 3. Instances -/

open ProfRegPR38 (registreMere registreFiliale mere filiale)
open ProfRegPR35 (registreBanque registreEmprunteur)

def auditeurExterne : Entite := 60
def directionFinanciereDuGroupe : Entite := 61

/-- **PR-42 (1) — mère et filiale.** Le prêt intragroupe est une écriture
    duale concordante (PR-38) ; sous contrôle commun, elle ne fait pas
    preuve seule ; confirmée par un auditeur externe non lié, elle fait
    preuve. -/
theorem sous_controle_la_duale_ne_prouve_pas_seule :
    EcritureDuale registreMere registreFiliale
    ∧ ¬ Probante .controleCommun registreMere registreFiliale none
    ∧ Probante .controleCommun registreMere registreFiliale
        (some ⟨auditeurExterne, false, .confirme⟩) := by
  decide

/-- **PR-42 (2) — un témoin du groupe ne suffit pas.** La direction
    financière du groupe est un tiers par rapport aux deux teneurs, mais
    elle leur est liée : sa confirmation ne rend pas l'écriture probante. -/
theorem un_temoin_du_groupe_ne_suffit_pas :
    ¬ Probante .controleCommun registreMere registreFiliale
        (some ⟨directionFinanciereDuGroupe, true, .confirme⟩) := by
  decide

/-- **PR-42 (3) — entre indépendants, l'écriture duale suffit.** La banque
    et l'emprunteur (AX-15). -/
theorem entre_independants_la_duale_suffit :
    Probante .independants registreBanque registreEmprunteur none := by
  decide

/-! ## 4. Instance : l'entreprise et le collectif d'employés (subordination) -/

def entrepriseE : Entite := 2
def collectifEmployes : Entite := 30
def expertExterne : Entite := 62

def regEntreprise : Registre Nat := ⟨entrepriseE, [⟨collectifEmployes, .Dplus, 50⟩]⟩
def regCollectif  : Registre Nat := ⟨collectifEmployes, [⟨entrepriseE, .Cplus, 50⟩]⟩

/-- **PR-42 (4) — subordination.** Même règle : le miroir inscrit par le
    collectif ne prouve pas seul ; confirmé par un expert externe non lié,
    il prouve ; l'employeur ne peut pas se confirmer lui-même. -/
theorem sous_subordination_meme_regle :
    EcritureDuale regEntreprise regCollectif
    ∧ ¬ Probante .subordination regEntreprise regCollectif none
    ∧ ¬ Probante .subordination regEntreprise regCollectif
          (some ⟨entrepriseE, false, .confirme⟩)
    ∧ Probante .subordination regEntreprise regCollectif
          (some ⟨expertExterne, false, .confirme⟩) := by
  decide

/-- **Témoin discriminant** (R-7) de `Probante` : les mêmes registres,
    selon la relation et le témoin. -/
theorem probante_temoin_discriminant :
    Probante .independants regEntreprise regCollectif none
    ∧ ¬ Probante .subordination regEntreprise regCollectif none := by
  decide

end ProfRegPR42
