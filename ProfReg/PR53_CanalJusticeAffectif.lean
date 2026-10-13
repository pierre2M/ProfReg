import ProfReg.PR52_QualificationAffective
import ProfReg.PR33_EffetDuDefaut

/-
  PR-53 · Canal G-JUSTICE → G-AFFECTIF (NT-G7 §4.3 ; NT-G9 §4.2, §10.2)
  =====================================================================

  Une injustice épistémique documentée en F6 (G-JUSTICE) passe en F1
  (G-AFFECTIF) comme **hypothèse explicative**, jamais comme qualification.
  Décisions du porteur (12/10/2026, fichier d'état §2, n° 37 à 40) :

  · types admis : TESTIMONIALE, HERMENEUTIQUE (CONTRIBUTOIRE retirée) ;
  · filtre qualitatif : portée SYSTEMATIQUE **ou** persistance STRUCTURELLE ;
    le filtre n'écarte que ce qui est **déclaré** incident (LOCALE et
    EPISODIQUE) ; une portée ou une persistance non déclarée passe, marquée ;
  · l'injustice doit être documentée **indépendamment** du signal de
    souffrance, par un documentant désigné ;
  · règle d'ordre : une qualification de dysfonctionnement sans examen de
    l'hypothèse pendante est E4 si elle est seulement inscrite, E3 si elle
    est mobilisée dans une décision touchant des personnes ;
  · `denidutravailreeldetecte` est **dérivé** (déni déclaré) ; un **déni
    présumé** est calculé sur les signaux qui empêchent la déclaration,
    au seul titre d'hypothèse.

  Ce fichier établit la **forme** de ces règles, non leur justesse.
  `[RÉSERVE DE MODÈLE]` Les structures sont réduites aux champs que les
  règles nomment. Lean 4 pur, sans Mathlib ; importe PR-52 et PR-33.

  Porteur : Pierre Musseau. Écrit le 12 octobre 2026.
-/

namespace ProfRegPR53

open ProfRegPR52

/-! ## 1. L'injustice documentée en F6 -/

/-- Types d'injustice épistémique en vigueur (CONTRIBUTOIRE retirée le
    12/10/2026). -/
inductive TypeInjustice where
  | testimoniale
  | hermeneutique
  | absente
  deriving DecidableEq, Repr

inductive Portee where
  | systematique
  | locale
  | nonDeclare
  deriving DecidableEq, Repr

inductive Persistance where
  | episodique
  | structurelle
  | nonDeclare
  deriving DecidableEq, Repr

/-- Une injustice épistémique inscrite en F6, réduite aux champs du canal.
    `issueDeLaSouffrance` lit `source_dynamique_souffrance` : vrai si la
    seule documentation de l'injustice est le signal de souffrance venu de
    G-AFFECTIF. -/
structure Injustice where
  type : TypeInjustice
  portee : Portee
  persistance : Persistance
  documentant : Option Nat
  issueDeLaSouffrance : Bool
  deriving DecidableEq, Repr

def typeAdmis : TypeInjustice → Bool
  | .testimoniale => true
  | .hermeneutique => true
  | .absente => false

/-- Le filtre qualitatif : n'est écarté que ce qui est déclaré incident. -/
def declareeIncidente (i : Injustice) : Bool :=
  i.portee == Portee.locale && i.persistance == Persistance.episodique

/-- **La règle de passage** (NT-ARCH F6, R-HYPOTHESE-INJUSTICE). -/
def passe (i : Injustice) : Bool :=
  typeAdmis i.type && !declareeIncidente i && i.documentant.isSome && !i.issueDeLaSouffrance

/-- Le marqueur `[PORTÉE NON DÉCLARÉE]` : l'injustice passe, sans que sa
    portée ou sa persistance soit déclarée. -/
def marqueePorteeNonDeclaree (i : Injustice) : Bool :=
  passe i && (i.portee == Portee.nonDeclare || i.persistance == Persistance.nonDeclare)

/-! ## 2. Le filtre -/

/-- **PR-53 (1) — le filtre n'écarte que ce qui est déclaré incident.**
    Une injustice de type admis, documentée par un documentant désigné et
    indépendamment de la souffrance, qui ne passe pas, est déclarée locale
    **et** épisodique. -/
theorem le_filtre_n_ecarte_que_le_declare_incident (i : Injustice)
    (ht : typeAdmis i.type = true) (hd : i.documentant.isSome = true)
    (hs : i.issueDeLaSouffrance = false) (hp : passe i = false) :
    i.portee = Portee.locale ∧ i.persistance = Persistance.episodique := by
  cases i with
  | mk t p q d s =>
    simp only [passe, declareeIncidente] at hp ht hd hs
    rw [ht, hd, hs] at hp
    cases p <;> cases q <;> simp_all

/-- **PR-53 (2) — « ou » : local mais structurel passe.** Le cas typique
    des collectifs de NT-G9 — une injustice locale à une équipe, mais
    installée — n'est pas écarté. -/
theorem local_mais_structurel_passe :
    passe ⟨.testimoniale, .locale, .structurelle, some 1, false⟩ = true := rfl

/-- **PR-53 (3) — la non-déclaration n'écarte pas : elle marque.** -/
theorem non_declare_passe_avec_marqueur :
    marqueePorteeNonDeclaree ⟨.hermeneutique, .nonDeclare, .nonDeclare, some 1, false⟩ = true := rfl

/-- **PR-53 (4) — une injustice documentée par la seule souffrance ne
    passe pas** (indépendance ; CONV-19). -/
theorem documentee_par_la_souffrance_ne_passe_pas (i : Injustice)
    (h : i.issueDeLaSouffrance = true) : passe i = false := by
  simp [passe, h]

/-- **Témoin discriminant** du filtre : la même injustice passe ou non selon
    qu'elle est déclarée structurelle ou épisodique (portée locale). -/
theorem filtre_temoin_discriminant :
    passe ⟨.testimoniale, .locale, .structurelle, some 1, false⟩ = true
  ∧ passe ⟨.testimoniale, .locale, .episodique, some 1, false⟩ = false := ⟨rfl, rfl⟩

/-! ## 3. L'hypothèse ne qualifie pas -/

/-- Ce que l'hypothèse apporterait à F1 si on la lisait comme une
    qualification : aucune source de qualification (F6 n'en est pas une). -/
def qualificationTireeDeLHypothese (q : Qualification) : Qualification :=
  { q with source := none }

/-- **PR-53 (5) — l'hypothèse seule ne qualifie pas le régime affectif.**
    Une qualification dont la seule source serait l'hypothèse venue de F6
    n'est pas légitime (CONV-20, PR-52). -/
theorem l_hypothese_seule_ne_qualifie_pas_le_regime (q : Qualification) :
    ¬ Legitime (qualificationTireeDeLHypothese q) :=
  sans_source_rien_n_est_legitime _ rfl

/-! ## 4. Le cycle A→J→A et sa terminaison -/

/-- L'état couplé : le signal de souffrance (G-AFFECTIF), l'injustice
    documentée (G-JUSTICE) et l'hypothèse pendante (F1). -/
structure EtatAJ where
  souffrance : Bool
  injustice : Injustice
  hypothese : Bool
  deriving DecidableEq, Repr

/-- **A→J** : la souffrance alimente F6 comme indice. Elle ne documente
    l'injustice que si celle-ci n'a pas d'autre documentation — d'où le
    drapeau `issueDeLaSouffrance`. -/
def canalAJ (e : EtatAJ) : EtatAJ :=
  if e.souffrance && e.injustice.documentant.isNone then
    { e with injustice := { e.injustice with issueDeLaSouffrance := true } }
  else e

/-- **J→A** : l'hypothèse pendante est ce que la règle de passage laisse
    passer ; elle ne lit pas la souffrance. -/
def canalJA (e : EtatAJ) : EtatAJ :=
  { e with hypothese := passe e.injustice }

/-- **PR-53 (6) — le cycle termine.** Un second passage A→J→A ne change
    rien : J→A ne relit pas ce que A→J écrit sur la souffrance, et A→J
    n'écrit rien dès que l'injustice a un documentant. -/
theorem le_cycle_AJ_termine (e : EtatAJ) :
    canalJA (canalAJ (canalJA (canalAJ e))) = canalJA (canalAJ e) := by
  rcases e with ⟨s, ⟨t, p, q, d, f⟩, h⟩
  cases s <;> cases d <;> simp [canalAJ, canalJA]

/-- **PR-53 (7) — et la souffrance ne se confirme pas elle-même.** Sans
    documentant, une souffrance déclarée ne fait passer aucune hypothèse :
    la boucle « souffrance → injustice → hypothèse » est coupée. -/
theorem la_souffrance_ne_se_confirme_pas_elle_meme (t : TypeInjustice)
    (p : Portee) (q : Persistance) (h : Bool) :
    (canalJA (canalAJ ⟨true, ⟨t, p, q, none, false⟩, h⟩)).hypothese = false := by
  simp [canalAJ, canalJA, passe]

/-! ## 5. Le déni du réel du travail : déclaré, présumé -/

/-- Les signaux de F1 et F6 qui empêchent la déclaration d'une atteinte
    (cas 1 à 5 de l'instruction du 12/10/2026). -/
structure SignauxDeni where
  ideologieDefensive : Bool
  activiteEmpechee : Bool
  hypotheseInjustice : Bool
  piegeReconnaissance : Bool
  deriving DecidableEq, Repr

/-- `sphereviolee`, réduite : atteinte déclarée à la contribution ou non. -/
inductive Sphere where
  | etreIdentite
  | faireContribution
  | nonDeclaree
  deriving DecidableEq, Repr

/-- **Déni déclaré** = `denidutravailreeldetecte` (valeur dérivée). -/
def deniDeclare (s : Sphere) : Bool := s == Sphere.faireContribution

/-- **Déni présumé** : aucune atteinte à la contribution déclarée, et un
    signal qui empêche de la déclarer. Hypothèse, jamais qualification. -/
def deniPresume (s : Sphere) (g : SignauxDeni) : Bool :=
  !deniDeclare s && (g.ideologieDefensive || g.activiteEmpechee
    || g.hypotheseInjustice || g.piegeReconnaissance)

/-- **PR-53 (8) — déclaré et présumé ne se recouvrent pas.** -/
theorem declare_et_presume_s_excluent (s : Sphere) (g : SignauxDeni) :
    ¬ (deniDeclare s = true ∧ deniPresume s g = true) := by
  cases s <;> simp [deniDeclare, deniPresume]

/-- **Témoin** : un déni présumé sans atteinte déclarée (cas 3, travail
    invisible : seule l'hypothèse herméneutique est pendante). -/
theorem deni_presume_temoin :
    deniPresume .nonDeclaree ⟨false, false, true, false⟩ = true
  ∧ deniPresume .nonDeclaree ⟨false, false, false, false⟩ = false := ⟨rfl, rfl⟩

/-! ## 6. La règle d'ordre et ses deux défauts (Annexe §A.15.11) -/

open ProfRegPR33 in
/-- Qualification de dysfonctionnement inscrite sans examen de l'hypothèse
    pendante : terme d'appréciation manquant, condition de bonne formation. -/
def ordreNonRespecteInscrite : Defaut :=
  { aucun with appreciation := true, conditionDeBonneFormation := true }

open ProfRegPR33 in
/-- La même, mobilisée dans une décision touchant des personnes : le défaut
    porte aussi sur l'attribution du trouble. -/
def ordreNonRespecteDecision : Defaut :=
  { ordreNonRespecteInscrite with attribution := true }

open ProfRegPR33 in
/-- **PR-53 (9) — deux défauts, deux effets.** Inscrite seulement : E4 ;
    mobilisée dans une décision : E3 (la branche 4 précède la branche 5). -/
theorem ordre_non_respecte_deux_effets :
    classer ordreNonRespecteInscrite = .E4 ∧ classer ordreNonRespecteDecision = .E3 := by
  decide

end ProfRegPR53
