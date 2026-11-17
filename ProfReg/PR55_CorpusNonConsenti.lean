/-
  PR-55 · CORPUS_NON_CONSENTI : signal, blocage et sortie (NT-G4 §3.2, §6 ;
  NT-ARCH F3 §3.3, F10)
  ==========================================================================

  Décisions du porteur (12/10/2026, fichier d'état §2, n° 42 et 43) :

  · **condition du signal** — `consentement_explicitation_corpus = FAUX` et
    `mode_validation_concept = EXPERTAL`. La condition antérieure portait sur
    « regime = EXPERTAL », valeur que le champ `regime_inscription_corpus` ne
    prend pas : le signal ne pouvait pas se lever ;
  · **sortie du blocage** — deux clés, combinées acteur par acteur : le
    **consentement obtenu après coup** (VC, Annexe H.2), ou la **représentation
    des absents** (F10 : absence justifiée — structurelle, ou recherche du
    consentement tracée et restée sans réponse —, mécanisme de substitution,
    porteur désigné). Aucune autre clé : un changement ultérieur du mode de
    validation ne lève pas le blocage.

  NT-G4 §6 pose une condition de réfutation : un blocage « systématique sans
  recours » ferait de R-HERMENEUTIQUE un verrou absolu. Ce fichier montre que
  l'absence n'est jamais un verrou (§3), et que le refus d'un acteur joignable
  n'est pas levé par la représentation (§3) : c'est un recours exercé, non un
  défaut de recours.

  Ce fichier établit la **forme** de ces règles, non leur justesse.
  `[RÉSERVE DE MODÈLE]` Acteurs et porteurs codés par leurs champs ; le
  consentement par acteur est l'attestation VC, le champ de corpus
  `consentement_explicitation_corpus` est la déclaration sur laquelle le signal
  se calcule. Lean 4 pur, sans Mathlib, sans import.

  Porteur : Pierre Musseau. Écrit le 12 octobre 2026.
-/

namespace ProfRegPR55

/-! ## 1. Le modèle -/

/-- `mode_validation_concept` (NT-ARCH F3, C-INSCRIPTION-CORPUS). -/
inductive ModeValidation where
  | consensuel | majoritaire | expertal | conteste
  deriving DecidableEq, Repr

/-- Situation d'un acteur dont le corpus est explicité. -/
inductive Absence where
  /-- Joignable : son consentement peut être demandé. -/
  | joignable
  /-- `absencestructurelle = VRAI` (F10) : ne peut par nature être présent. -/
  | structurelle
  /-- Recherche du consentement tracée, restée sans réponse. -/
  | rechercheInfructueuse
  deriving DecidableEq, Repr

structure Acteur where
  /-- Consentement attesté (VC), y compris obtenu après coup. -/
  consentement : Bool
  absence : Absence
  /-- `porteurrepresentationabsents` (F10). -/
  porteur : Option Nat
  /-- `mecanismesubstitution` renseigné (F10). -/
  mecanisme : Bool
  deriving DecidableEq, Repr

structure Corpus where
  consentementCorpus : Bool
  mode : ModeValidation
  /-- Le signal a été inscrit ; il reste inscrit jusqu'à la levée. -/
  signale : Bool
  concernes : List Acteur
  deriving DecidableEq, Repr

/-- **CORPUS_NON_CONSENTI** (condition réécrite le 12/10/2026). -/
def signal (c : Corpus) : Bool := !c.consentementCorpus && c.mode == ModeValidation.expertal

/-- Représentation des absents (F10) : absence justifiée, porteur, mécanisme. -/
def represente (a : Acteur) : Bool :=
  a.absence != Absence.joignable && a.porteur.isSome && a.mecanisme

/-- **Les deux clés, combinées.** -/
def couvert (a : Acteur) : Bool := a.consentement || represente a

def leve (c : Corpus) : Bool := c.concernes.all couvert

/-- R-HERMENEUTIQUE : blocage de DÉLIBÉRATION. -/
def bloque (c : Corpus) : Bool := c.signale && !leve c

/-! ## 2. Le signal -/

/-- **PR-55 (1) — le signal lit le mode de validation.** `[LECTURE — dépliage
    de `signal`]` Témoin : `corpus_signal_temoin_discriminant`. -/
theorem corpus_non_consenti_lit_le_mode_de_validation (c : Corpus) :
    signal c = true ↔ c.consentementCorpus = false ∧ c.mode = ModeValidation.expertal := by
  cases c with
  | mk k m s l => cases k <;> cases m <;> simp [signal]

/-- **Témoin discriminant** : le même corpus non consenti signale sous
    validation experte, non sous validation majoritaire. -/
theorem corpus_signal_temoin_discriminant :
    signal ⟨false, .expertal, false, []⟩ = true ∧ signal ⟨false, .majoritaire, false, []⟩ = false :=
  ⟨rfl, rfl⟩

/-! ## 3. La sortie -/

/-- **PR-55 (2) — la représentation ne couvre pas un acteur joignable.** Un
    acteur joignable qui n'a pas consenti n'est couvert par aucun porteur ni
    aucun mécanisme : la représentation ne contourne pas le consentement. -/
theorem la_representation_ne_couvre_pas_un_joignable (a : Acteur)
    (hj : a.absence = Absence.joignable) (hc : a.consentement = false) : couvert a = false := by
  simp [couvert, represente, hj, hc]

/-- Désigner un porteur et un mécanisme pour chaque absent. -/
def completer (c : Corpus) : Corpus :=
  { c with concernes := c.concernes.map (fun a =>
      if a.absence == Absence.joignable then a else { a with porteur := some 0, mecanisme := true }) }

/-- **PR-55 (3) — l'absence n'est jamais un verrou.** Si chaque acteur a
    consenti ou est absent, désigner un porteur et un mécanisme pour les absents
    lève le blocage. La condition de réfutation de NT-G4 §6 ne se réalise pas
    par l'absence. -/
theorem l_absence_n_est_jamais_un_verrou (c : Corpus)
    (h : ∀ a ∈ c.concernes, a.consentement = true ∨ a.absence ≠ Absence.joignable) :
    bloque (completer c) = false := by
  have hl : leve (completer c) = true := by
    simp only [leve, completer, List.all_map, List.all_eq_true]
    intro a ha
    rcases h a ha with hc | hj
    · by_cases hb : a.absence = Absence.joignable <;> simp [couvert, represente, hc, hb]
    · simp [couvert, represente, hj]
  simp [bloque, hl]

/-- **PR-55 (4) — les deux clés sont nécessaires.** Un corpus qui concerne un
    acteur joignable consentant et un absent structurel représenté est levé ;
    le consentement seul ne couvre pas l'absent, la représentation seule ne
    couvre pas le joignable. -/
theorem les_deux_cles_sont_necessaires :
    let j : Acteur := ⟨true, .joignable, none, false⟩
    let s : Acteur := ⟨false, .structurelle, some 1, true⟩
    leve ⟨false, .expertal, true, [j, s]⟩ = true
  ∧ s.consentement = false ∧ represente j = false := ⟨rfl, rfl, rfl⟩

/-- **PR-55 (5) — un changement du mode de validation ne lève pas le
    blocage.** Le blocage ne lit pas le mode : une fois le signal inscrit, seule
    une des deux clés le lève. `[LECTURE — dépliage de `bloque`]` Témoin :
    `bloque_temoin_discriminant`. -/
theorem le_changement_de_mode_ne_leve_pas (c : Corpus) (m : ModeValidation) :
    bloque { c with mode := m } = bloque c := rfl

/-- **Témoin discriminant** du blocage : le même absent, sans porteur, bloque ;
    avec porteur et mécanisme, ne bloque plus. -/
theorem bloque_temoin_discriminant :
    bloque ⟨false, .expertal, true, [⟨false, .rechercheInfructueuse, none, false⟩]⟩ = true
  ∧ bloque ⟨false, .expertal, true, [⟨false, .rechercheInfructueuse, some 1, true⟩]⟩ = false :=
  ⟨rfl, rfl⟩

end ProfRegPR55
