/-
  PR-52 · Qualification du régime affectif (NT-G9 ; CONV-19, CONV-20)
  =====================================================================

  NT-G9 §10.1 pose deux règles sur l'inscription d'une qualification du
  régime affectif, et §4.2 une règle de non-confusion :

  · **règle d'inscription** — `sourcequalification ≠ INDÉTERMINÉE` est
    nécessaire et non suffisant ; il faut en outre
    `consentementcollectif = true` et
    `statut_rgpd_regimeaffectif ∈ {ANONYMISE, PSEUDONYMISE, AGREGESEUL}` ;
  · **règle du support** `[ENGAGEMENT À HORIZON IRRÉVERSIBLE]` — aucune
    inscription de `regimeaffectif` n'est bien formée sur support
    distribué tant que `statut_rgpd_regimeaffectif ≠ NONCOLLECTE` ;
  · **non-confusion** — `signalsouffrance` est un indice explicatif, jamais
    le fondement normatif d'une créance.

  CONV-20 porte les deux premières, CONV-19 la troisième (Annexe §A.15.16,
  §A.15.17). Ce fichier en établit la **forme**, jamais la justesse : une
  qualification bien formée peut être fausse ou contestée.

  CE QUE LA FORMALISATION FAIT VOIR
  ---------------------------------
  Les deux règles de §10.1, **composées**, ferment toute inscription sur
  support distribué : la règle du support exige `NONCOLLECTE`, la règle
  d'inscription l'exclut (§3). C'est conforme à ce que NT-G9 écrit
  (« inopérant par construction ») ; c'est aussi dire que `NONCOLLECTE`
  n'est jamais une qualification légitime. **Décision du porteur
  (12/10/2026)** : `NONCOLLECTE` désigne l'absence de toute qualification
  inscrite — seule l'existence des traces est tenue ; NT-G9 §10.1 est
  reformulé en ce sens. Le théorème de §3 en est la forme.

  `[RÉSERVE DE MODÈLE]` `Qualification` réduit l'inscription aux quatre
  champs que les règles nomment ; `Appui` réduit les appuis d'une créance
  à deux classes. Lean 4 pur, sans Mathlib, sans import.

  Porteur : Pierre Musseau. Écrit le 12 octobre 2026.
-/

namespace ProfRegPR52

/-! ## 1. Le modèle -/

/-- Les trois sources admises de `sourcequalification` (NT-G9 §3.1). La
    valeur `INDÉTERMINÉE` est l'absence de source : `none` ci-dessous. -/
inductive SourceQualification where
  | cliniqueExterne
  | dialogueProfessionnel
  | archivageDesActes
  deriving DecidableEq, Repr

/-- `statut_rgpd_regimeaffectif` (NT-G9 §10.1). -/
inductive StatutRGPD where
  | anonymise
  | pseudonymise
  | agregeSeul
  | nonCollecte
  deriving DecidableEq, Repr

/-- Le support de l'inscription. -/
inductive Support where
  | local
  | distribue
  deriving DecidableEq, Repr

/-- Une qualification du régime affectif, réduite aux champs que les
    règles de NT-G9 §10.1 nomment. -/
structure Qualification where
  source : Option SourceQualification
  consentementCollectif : Bool
  statut : StatutRGPD
  support : Support
  deriving DecidableEq, Repr

/-- Les trois statuts que la règle d'inscription admet. -/
def statutProtecteur : StatutRGPD → Bool
  | .anonymise => true
  | .pseudonymise => true
  | .agregeSeul => true
  | .nonCollecte => false

/-- **Règle d'inscription** (NT-G9 §10.1 ; CONV-20, premier membre). -/
def Legitime (q : Qualification) : Prop :=
  q.source ≠ none ∧ q.consentementCollectif = true ∧ statutProtecteur q.statut = true

/-- **Règle du support** (NT-G9 §10.1 ; CONV-20, second membre). -/
def SupportAdmis (q : Qualification) : Prop :=
  q.support = Support.distribue → q.statut = StatutRGPD.nonCollecte

/-- Une qualification est inscriptible si les deux règles tiennent. -/
def Inscriptible (q : Qualification) : Prop :=
  Legitime q ∧ SupportAdmis q

/-! ## 2. La règle d'inscription -/

/-- **PR-52 (1) — sans source déclarée, rien n'est légitime.**
    `[LECTURE — dépliage de `Legitime`]` Témoin : `inscriptible_temoin_discriminant`. -/
theorem sans_source_rien_n_est_legitime (q : Qualification)
    (h : q.source = none) : ¬ Legitime q :=
  fun hl => hl.1 h

/-- **PR-52 (2) — la source est nécessaire, non suffisante.** Une
    qualification de source clinique externe, sans consentement collectif,
    n'est pas légitime. -/
theorem la_source_ne_suffit_pas :
    ∃ q : Qualification, q.source ≠ none ∧ ¬ Legitime q :=
  ⟨⟨some .cliniqueExterne, false, .pseudonymise, .local⟩,
   by simp,
   fun hl => Bool.noConfusion hl.2.1⟩

/-- **PR-52 (3) — `NONCOLLECTE` n'est jamais légitime.**
    `[LECTURE — dépliage de `Legitime`]` Témoin : `inscriptible_temoin_discriminant`
    (statut `AGREGESEUL`, légitime). -/
theorem noncollecte_n_est_jamais_legitime (q : Qualification)
    (h : q.statut = StatutRGPD.nonCollecte) : ¬ Legitime q := by
  intro hl
  have hp := hl.2.2
  rw [h] at hp
  exact Bool.noConfusion hp

/-! ## 3. Les deux règles composées -/

/-- **PR-52 (4) — sur support distribué, aucune qualification n'est
    inscriptible.** La règle du support exige `NONCOLLECTE` ; la règle
    d'inscription l'exclut. C'est le résultat du fichier : l'engagement
    irréversible est rendu inopérant par construction (NT-G9 §10.1), et
    cela vaut pour **toute** qualification, quelle que soit sa source. -/
theorem sur_support_distribue_rien_n_est_inscriptible (q : Qualification)
    (h : q.support = Support.distribue) : ¬ Inscriptible q :=
  fun ⟨hl, hs⟩ => noncollecte_n_est_jamais_legitime q (hs h) hl

/-- **Témoin discriminant** de `Inscriptible` : une qualification
    inscriptible (dialogue professionnel, consentement, agrégé seul,
    support local) et une qui ne l'est pas (source indéterminée). -/
theorem inscriptible_temoin_discriminant :
    (∃ q : Qualification, Inscriptible q) ∧ (∃ q : Qualification, ¬ Inscriptible q) :=
  ⟨⟨⟨some .dialogueProfessionnel, true, .agregeSeul, .local⟩,
     ⟨⟨by simp, rfl, rfl⟩, fun h => Support.noConfusion h⟩⟩,
   ⟨⟨none, true, .agregeSeul, .local⟩, fun hi => hi.1.1 rfl⟩⟩

/-! ## 4. La non-confusion (CONV-19) -/

/-- Les appuis d'une qualification de créance, réduits à deux classes :
    le signal de souffrance (G-AFFECTIF) et un appui de G-JUSTICE. -/
inductive Appui where
  | signalSouffrance
  | appuiJustice
  deriving DecidableEq, Repr

/-- **CONV-19, encodée.** Une créance n'est qualifiée que par un appui
    autre que le signal de souffrance. -/
def QualifieCreance (appuis : List Appui) : Prop :=
  ∃ a ∈ appuis, a ≠ Appui.signalSouffrance

/-- **PR-52 (5) — la souffrance seule ne qualifie aucune créance.**
    `[LECTURE — dépliage de `QualifieCreance`, qui encode CONV-19]` Témoin :
    `la_souffrance_n_empeche_pas_la_qualification`. -/
theorem la_souffrance_seule_ne_qualifie_aucune_creance (appuis : List Appui)
    (h : ∀ a ∈ appuis, a = Appui.signalSouffrance) : ¬ QualifieCreance appuis :=
  fun ⟨a, ha, hne⟩ => hne (h a ha)

/-- **PR-52 (6) — et elle n'y fait pas obstacle.** Un signal de souffrance
    joint à un appui de G-JUSTICE n'empêche pas la qualification : la
    souffrance n'est ni une preuve ni une disqualification (NT-G9 §4.2). -/
theorem la_souffrance_n_empeche_pas_la_qualification :
    QualifieCreance [Appui.signalSouffrance, Appui.appuiJustice] :=
  ⟨Appui.appuiJustice, by simp, fun h => Appui.noConfusion h⟩

end ProfRegPR52
