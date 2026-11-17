import ProfReg.PR55_CorpusNonConsenti

/-
  PR-56 · Consentement par personne ; absence opposable (NT-G4 §6bis ;
  NT-ARCH F3, C-INSCRIPTION-CORPUS, §3.3)
  =====================================================================

  Décisions du porteur (12/10/2026, fichier d'état §2, n° 45 et 46) :

  · **consentement par personne** — C-INSCRIPTION-CORPUS porte la liste
    `consentements_attestes` (DID + VC) ; `consentement_explicitation_corpus`
    devient **dérivé** : VRAI si et seulement si chaque personne du périmètre
    déclaré a un consentement attesté ;
  · **absence opposable** — l'absence au titre d'une « recherche infructueuse »
    n'est admise que si elle est **opposable** : une trace minimale de la
    recherche (au moins une tentative datée, avec son canal) **ou** une
    attestation de l'instance de contrôle ; et elle tombe si une contestation
    est retenue par l'instance (la personne s'est manifestée, ou la recherche
    est démentie). L'absence structurelle (F10 `absencestructurelle`) reste
    admise sans trace.

  PR-55 établit la forme du signal et de la sortie sur des absences
  **déclarées** ; PR-56 la **restreint** : il n'admet jamais plus de
  représentations que PR-55 (§3). Ce fichier établit la forme de ces règles,
  non leur justesse ; il ne dit pas qu'une trace est sincère — il dit qu'elle
  existe et qu'elle est contestable.

  `[RÉSERVE DE MODÈLE]` Une tentative est un couple (date, canal) codé par
  des entiers ; la contestation est réduite à son issue (retenue ou non).
  Lean 4 pur, sans Mathlib ; importe PR-55.

  Porteur : Pierre Musseau. Écrit le 12 octobre 2026.
-/

namespace ProfRegPR56

open ProfRegPR55

/-! ## 1. Le modèle -/

/-- La recherche du consentement d'une personne. -/
structure Recherche where
  /-- Tentatives consignées : (date, canal). -/
  tentatives : List (Nat × Nat)
  /-- Attestation de la recherche par l'instance de contrôle. -/
  attestation : Bool
  /-- Une contestation a été retenue par l'instance. -/
  contestationRetenue : Bool
  deriving DecidableEq, Repr

/-- Une personne du périmètre déclaré : ses champs PR-55 et sa recherche. -/
structure Personne where
  base : Acteur
  recherche : Recherche
  deriving DecidableEq, Repr

/-- **Consentement global dérivé** (`consentement_explicitation_corpus`). -/
def consentementDerive (perimetre : List Personne) : Bool :=
  perimetre.all (fun p => p.base.consentement)

/-- Une recherche est **opposable** : trace ou attestation, et aucune
    contestation retenue. -/
def opposable (r : Recherche) : Bool :=
  (!r.tentatives.isEmpty || r.attestation) && !r.contestationRetenue

/-- **Absence admise.** -/
def absenceAdmise (p : Personne) : Bool :=
  match p.base.absence with
  | .joignable => false
  | .structurelle => true
  | .rechercheInfructueuse => opposable p.recherche

def representeOpp (p : Personne) : Bool :=
  absenceAdmise p && p.base.porteur.isSome && p.base.mecanisme

def couvertOpp (p : Personne) : Bool := p.base.consentement || representeOpp p

def leveOpp (perimetre : List Personne) : Bool := perimetre.all couvertOpp

/-! ## 2. Le consentement global est dérivé -/

/-- **PR-56 (1) — le consentement du corpus est vrai si et seulement si chaque
    personne du périmètre a consenti.** `[LECTURE — dépliage de
    `consentementDerive`]` Témoin : `consentement_derive_temoin`. -/
theorem le_consentement_du_corpus_est_derive (l : List Personne) :
    consentementDerive l = true ↔ ∀ p ∈ l, p.base.consentement = true := by
  simp [consentementDerive]

/-- **Témoin** : un seul consentement manquant suffit à rendre le
    consentement du corpus faux. -/
theorem consentement_derive_temoin :
    let r : Recherche := ⟨[], false, false⟩
    consentementDerive [⟨⟨true, .joignable, none, false⟩, r⟩] = true
  ∧ consentementDerive [⟨⟨true, .joignable, none, false⟩, r⟩,
                        ⟨⟨false, .structurelle, some 1, true⟩, r⟩] = false := ⟨rfl, rfl⟩

/-! ## 3. L'absence opposable -/

/-- **PR-56 (2) — une recherche sans trace ni attestation n'est pas une
    absence.** Quels que soient le porteur et le mécanisme désignés, la
    personne n'est pas représentée. -/
theorem sans_trace_ni_attestation_pas_d_absence (p : Personne)
    (ha : p.base.absence = .rechercheInfructueuse)
    (ht : p.recherche.tentatives = []) (hat : p.recherche.attestation = false) :
    representeOpp p = false := by
  simp [representeOpp, absenceAdmise, opposable, ha, ht, hat]

/-- **PR-56 (3) — une contestation retenue fait tomber la représentation**,
    même avec trace et attestation. -/
theorem une_contestation_retenue_fait_tomber_la_representation (p : Personne)
    (ha : p.base.absence = .rechercheInfructueuse)
    (hc : p.recherche.contestationRetenue = true) : representeOpp p = false := by
  simp [representeOpp, absenceAdmise, opposable, ha, hc]

/-- **Témoin discriminant** : la trace seule, l'attestation seule suffisent ;
    ni l'une ni l'autre, non. -/
theorem trace_ou_attestation_temoin :
    let b : Acteur := ⟨false, .rechercheInfructueuse, some 1, true⟩
    representeOpp ⟨b, ⟨[(20261012, 1)], false, false⟩⟩ = true
  ∧ representeOpp ⟨b, ⟨[], true, false⟩⟩ = true
  ∧ representeOpp ⟨b, ⟨[], false, false⟩⟩ = false := ⟨rfl, rfl, rfl⟩

/-- **PR-56 (4) — PR-56 restreint PR-55.** Toute représentation admise ici
    l'est par PR-55 ; la réciproque est fausse (`trace_ou_attestation_temoin`,
    troisième membre). -/
theorem pr56_restreint_pr55 (p : Personne) (h : representeOpp p = true) :
    represente p.base = true := by
  rcases p with ⟨⟨c, a, po, m⟩, r⟩
  cases a <;> simp_all [representeOpp, absenceAdmise, represente]

/-! ## 4. L'absence justifiée n'est jamais un verrou -/

/-- Désigner un porteur et un mécanisme pour chaque personne absente. -/
def completer (l : List Personne) : List Personne :=
  l.map (fun p =>
    if p.base.absence == .joignable then p
    else { p with base := { p.base with porteur := some 0, mecanisme := true } })

/-- **PR-56 (5) — l'absence opposable n'est jamais un verrou.** Si chaque
    personne a consenti ou est absente à titre admis, désigner un porteur et
    un mécanisme pour les absents lève le blocage. -/
theorem l_absence_opposable_n_est_jamais_un_verrou (l : List Personne)
    (h : ∀ p ∈ l, p.base.consentement = true ∨ absenceAdmise p = true) :
    leveOpp (completer l) = true := by
  simp only [leveOpp, completer, List.all_map, List.all_eq_true]
  intro p hp
  rcases h p hp with hc | ha
  · by_cases hb : p.base.absence = .joignable <;> simp [couvertOpp, hc, hb]
  · have hj : p.base.absence ≠ .joignable := by
      intro hj; simp [absenceAdmise, hj] at ha
    have ha' : absenceAdmise { p with base := { p.base with porteur := some 0, mecanisme := true } } = true := by
      simpa [absenceAdmise] using ha
    simp [couvertOpp, representeOpp, hj, ha']

end ProfRegPR56
