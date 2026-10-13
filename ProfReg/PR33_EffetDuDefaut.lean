/-!
# PR-33 — L'effet du défaut : codes E0-E7 et critère ordonné (Annexe §A.15.11)

28 septembre 2026. Décision du porteur (piste 7 de la note
`ProfReg/Note_Critere_Refus_Marqueur_2026-09-28.md`) : ancrer le critère de
l'effet du défaut.

**Ce que ce fichier établit, et ce qu'il n'établit pas.** Le critère est une
**règle d'architecture déclarée** : il ne se démontre pas. Les théorèmes
ci-dessous en établissent la **forme** — l'ordre des branches compte, un refus
ne vient que des branches 1 à 3, un marqueur ne vient que de l'appréciation ou
du statut candidat — et le **classement de référence** des règles décidées.

**Branche 1bis (12 octobre 2026, décision du porteur).** *L'inscription est
elle-même le dommage* : quand la règle protège contre l'enregistrement même
(données sensibles sans base de légitimité, support irréversible), le défaut
produit un refus, avant toute branche de traitement. Elle appartient au bloc
des refus : « branches 1 à 3 » s'entend 1bis comprise. Premier cas : CONV-20.
Ils ne disent pas qu'une règle est bien classée : le classement d'une règle
réelle dans un `Defaut` est une **lecture déclarée**.

`[RÉSERVE DE MODÈLE]` Les effets hors critère (E2, E6, E7) ne sont pas produits
par `classer` : ils ne portent pas sur l'inscription. Le statut candidat à
horizon de la branche 3 (`CANDIDAT_NON_INSTANCIABLE`) est codé **E4** —
inscrit, sans effet, avec horizon —, par l'homologie déclarée en C-9.
Lean pur, sans import.
-/

namespace ProfRegPR33

inductive Effet where
  | E0 | E1 | E2 | E3 | E4 | E5 | E6 | E7
  deriving DecidableEq, Repr

/-- Un défaut de bonne formation, décrit par les questions du critère. -/
structure Defaut where
  sansObjet                 : Bool   -- branche 1
  inscriptionDommageable    : Bool   -- branche 1bis
  nonDeclarationRenommee    : Bool   -- branche 2
  conditionneDAutres        : Bool   -- branche 3
  candidatAHorizon          : Bool   -- exception de la branche 3
  attribution               : Bool   -- branche 4
  appreciation              : Bool   -- branche 5
  conditionDeBonneFormation : Bool   -- branche 5 : E4 si vrai, E5 sinon
  deriving DecidableEq, Repr

/-- **Le critère, dans l'ordre** : la première branche satisfaite fixe l'effet. -/
def classer (d : Defaut) : Effet :=
  if d.sansObjet then .E1
  else if d.inscriptionDommageable then .E1
  else if d.nonDeclarationRenommee then .E1
  else if d.conditionneDAutres then (if d.candidatAHorizon then .E4 else .E1)
  else if d.attribution then .E3
  else if d.appreciation then (if d.conditionDeBonneFormation then .E4 else .E5)
  else .E0

def aucun : Defaut := ⟨false, false, false, false, false, false, false, false⟩

/-! ## Les règles décidées, lues comme défauts (lectures déclarées) -/

def conv3 : Defaut := { aucun with sansObjet := true, attribution := true }
def conv7 : Defaut := { aucun with appreciation := true, conditionDeBonneFormation := true }
def conv8 : Defaut := { aucun with attribution := true }
def conv15 : Defaut := { aucun with appreciation := true }
def sansObjetNonMotive : Defaut := { aucun with nonDeclarationRenommee := true }
def regimeSansHorizon : Defaut := { aucun with conditionneDAutres := true }
def regimeCandidat : Defaut := { aucun with conditionneDAutres := true, candidatAHorizon := true }
def p5Principe : Defaut := { aucun with attribution := true, appreciation := true, conditionDeBonneFormation := true }
def p5Exception : Defaut := { aucun with appreciation := true, conditionDeBonneFormation := true }
def clotureNonDeclaree : Defaut := { aucun with appreciation := true, conditionDeBonneFormation := true }
/-- CONV-20 : qualification du régime affectif sans source, sans consentement,
    sans statut protecteur, ou sur support distribué. -/
def conv20 : Defaut := { aucun with inscriptionDommageable := true, appreciation := true, conditionDeBonneFormation := true }

/-- **Classement de référence** (Annexe §A.15.11) : chaque règle reçoit son code. -/
theorem classement_de_reference :
    classer conv3 = .E1 ∧ classer conv7 = .E4 ∧ classer conv8 = .E3
  ∧ classer conv15 = .E5 ∧ classer sansObjetNonMotive = .E1
  ∧ classer regimeSansHorizon = .E1 ∧ classer regimeCandidat = .E4
  ∧ classer p5Principe = .E3 ∧ classer p5Exception = .E4
  ∧ classer clotureNonDeclaree = .E4 ∧ classer conv20 = .E1 := by
  decide

/-- **L'ordre compte** : CONV-3 relève aussi de l'attribution ; c'est la branche 1
    qui l'emporte. Sans elle, le même défaut irait en DÉLIBÉRATION. -/
theorem l_ordre_fait_prevaloir_l_objet :
    classer conv3 = .E1 ∧ classer { conv3 with sansObjet := false } = .E3 := by
  decide

/-- **Branche 1bis — l'inscription dommageable est refusée avant tout marqueur.**
    Le même défaut, sans la branche 1bis, serait inscrit avec un marqueur (E4) :
    c'est ce que la protection de données sensibles interdit. -/
theorem l_inscription_dommageable_est_refusee_avant_tout_marqueur :
    classer conv20 = .E1 ∧ classer { conv20 with inscriptionDommageable := false } = .E4 := by
  decide

/-- **Mal formée ⇏ refusée** : CONV-7 porte sur une condition de bonne formation
    et n'est pas refusée. -/
theorem mal_formee_n_implique_pas_refusee :
    ∃ d : Defaut, d.conditionDeBonneFormation = true ∧ classer d ≠ .E1 :=
  ⟨conv7, rfl, by decide⟩

/-- **Un refus ne vient que des branches 1 à 3** (1bis comprise). -/
theorem les_refus_ne_viennent_que_des_branches_un_a_trois :
    ∀ a i b c h e f g : Bool, classer ⟨a, i, b, c, h, e, f, g⟩ = .E1 →
      (a = true ∨ i = true ∨ b = true ∨ c = true) := by
  decide

/-- **Un marqueur d'écriture mal formée (E4) ne vient que de l'appréciation, ou
    du statut candidat à horizon.** -/
theorem le_marqueur_ne_vient_que_de_l_appreciation_ou_du_candidat :
    ∀ a i b c h e f g : Bool, classer ⟨a, i, b, c, h, e, f, g⟩ = .E4 →
      ((f = true ∧ g = true) ∨ (c = true ∧ h = true)) := by
  decide

/-- **Sans branche, pas de classement** : un défaut qui ne relève d'aucune
    branche reste E0 — défaut de rédaction, ou effet hors critère. -/
theorem sans_branche_pas_de_classement (d : Defaut)
    (h₁ : d.sansObjet = false) (h₁b : d.inscriptionDommageable = false)
    (h₂ : d.nonDeclarationRenommee = false)
    (h₃ : d.conditionneDAutres = false) (h₄ : d.attribution = false)
    (h₅ : d.appreciation = false) : classer d = .E0 := by
  simp [classer, h₁, h₁b, h₂, h₃, h₄, h₅]

end ProfRegPR33
