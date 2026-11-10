import ProfReg.PR54_BoucleEtContrePerformativite

/-
  PR-57 · Phase RECHERCHE_INTERVENTION : constat d'effet et contre-performativité
  attestée (NT-ARCH §B.2ter ; NT-G4 §7, §8 ; NT-G10 §5)
  ==============================================================================

  Décisions du porteur (12/10/2026, fichier d'état §2, n° 47 à 50) :

  · RECHERCHE_INTERVENTION est une **phase** de C-ENQUETE-V5 : l'enquête
    publique démocratique au sens de Ferey (2024, ch. 5 §III, p. 319-325 ;
    ch. 2 §II, p. 138-141) ;
  · `hypothese_declaree` (la solution projetée, déclarée **avant** l'épreuve)
    et `effet_constate` ∈ {ALIGNÉ, CONTRAIRE, À QUALIFIER, NON INSTRUIT} ;
  · le constat n'est recevable que s'il est attesté par une instance d'enquête
    **distincte du porteur de l'instrument** et **associant les personnes
    concernées** (contrainte des spécialistes, Ferey p. 319) ;
  · le signal CONTRE_PERFORMATIVITE_ATTESTEE (constat CONTRAIRE recevable)
    **relance** la phase d'enquête, puis la délibération ; un constat
    À QUALIFIER relance l'enquête sans lever le signal (le cas des quotas
    chiliens, Ferey p. 141) ;
  · déclencheurs : contestation par une personne concernée, boucle
    confirmante, réfutation Goodhart (NT-G10), effet d'hôte ; l'échéance
    périodique seulement si la revue associe les concernés (Ferey p. 325).

  PR-54 établit que, hors effet d'hôte, aucun signal ne voit la
  contre-performativité. PR-57 établit que l'enquête la rend visible, **à la
  condition** qu'un constat recevable existe (§4) : la lacune est levée pour
  les cas instruits, non pour les autres.

  Ce fichier établit la forme de ces règles, non la justesse d'un constat.
  `[RÉSERVE DE MODÈLE]` Identités et dates codées par des entiers ;
  l'association des concernés réduite à un booléen. Lean 4 pur, sans Mathlib ;
  importe PR-54.

  Porteur : Pierre Musseau. Écrit le 12 octobre 2026.
-/

namespace ProfRegPR57

open ProfRegPR54

/-! ## 1. Le modèle -/

inductive EffetConstate where
  | aligne | contraire | aQualifier | nonInstruit
  deriving DecidableEq, Repr

/-- Un constat d'effet issu de la phase RECHERCHE_INTERVENTION. -/
structure Constat where
  effet : EffetConstate
  /-- DID de l'instance qui atteste. -/
  attestant : Nat
  /-- DID du porteur de l'instrument examiné. -/
  porteurInstrument : Nat
  /-- L'instance associe les personnes concernées. -/
  concernesAssocies : Bool
  /-- Date de `hypothese_declaree` ; `none` : non déclarée. -/
  dateHypothese : Option Nat
  dateConstat : Nat
  deriving DecidableEq, Repr

/-- Hypothèse déclarée avant le constat. -/
def hypotheseAnterieure (c : Constat) : Bool :=
  match c.dateHypothese with
  | some d => decide (d < c.dateConstat)
  | none => false

/-- **Recevabilité** d'un constat. -/
def recevable (c : Constat) : Bool :=
  c.attestant != c.porteurInstrument && c.concernesAssocies && hypotheseAnterieure c

/-- **CONTRE_PERFORMATIVITE_ATTESTEE.** -/
def signalCPA (c : Constat) : Bool := recevable c && c.effet == EffetConstate.contraire

/-- Un alignement attesté. -/
def alignementAtteste (c : Constat) : Bool := recevable c && c.effet == EffetConstate.aligne

/-- **Relance** de la phase d'enquête (puis délibération). -/
def relance (c : Constat) : Bool :=
  recevable c && (c.effet == EffetConstate.contraire || c.effet == EffetConstate.aQualifier)

/-! ## 2. La recevabilité -/

/-- **PR-57 (1) — NON INSTRUIT ne vaut pas ALIGNÉ**, et ne lève rien. -/
theorem non_instruit_ne_vaut_pas_aligne (c : Constat) (h : c.effet = .nonInstruit) :
    alignementAtteste c = false ∧ signalCPA c = false ∧ relance c = false := by
  simp [alignementAtteste, signalCPA, relance, h]

/-- **PR-57 (2) — le porteur ne s'atteste pas lui-même.** -/
theorem le_porteur_ne_s_atteste_pas (c : Constat) (h : c.attestant = c.porteurInstrument) :
    recevable c = false := by
  simp [recevable, h]

/-- **PR-57 (3) — sans les personnes concernées, pas de constat recevable**
    (contrainte des spécialistes). -/
theorem sans_les_concernes_pas_de_constat (c : Constat) (h : c.concernesAssocies = false) :
    recevable c = false := by
  simp [recevable, h]

/-- **PR-57 (4) — une hypothèse déclarée après le constat, ou jamais, n'est
    pas admise.** -/
theorem hypothese_apres_coup_non_admise (c : Constat)
    (h : ∀ d, c.dateHypothese = some d → c.dateConstat ≤ d) : recevable c = false := by
  cases hd : c.dateHypothese with
  | none => simp [recevable, hypotheseAnterieure, hd]
  | some d =>
    have := h d hd
    simp [recevable, hypotheseAnterieure, hd]
    omega

/-- **Témoin discriminant** : le même constat CONTRAIRE lève le signal s'il
    est attesté par un tiers associant les concernés, non s'il est attesté par
    le porteur. -/
theorem constat_temoin_discriminant :
    signalCPA ⟨.contraire, 2, 1, true, some 1, 5⟩ = true
  ∧ signalCPA ⟨.contraire, 1, 1, true, some 1, 5⟩ = false := ⟨rfl, rfl⟩

/-! ## 3. Le signal et la relance -/

/-- **PR-57 (5) — À QUALIFIER relance l'enquête sans lever le signal.** -/
theorem a_qualifier_relance_sans_signal (c : Constat) (hr : recevable c = true)
    (h : c.effet = .aQualifier) : relance c = true ∧ signalCPA c = false := by
  simp [relance, signalCPA, hr, h]

/-- Nombre de relances produites par une suite de constats. -/
def relances (l : List Constat) : Nat := l.countP (fun c => relance c)

/-- **PR-57 (6) — pas de relance sans constat.** Chaque relance est causée
    par un constat distinct : la phase ne boucle pas d'elle-même. -/
theorem pas_de_relance_sans_constat (l : List Constat) : relances l ≤ l.length :=
  List.countP_le_length

/-! ## 4. L'enquête et la lacune de PR-54 -/

/-- Ce que le registre voit, avec la phase d'enquête. -/
def vueAvecEnquete (e : EcritureP) (c : Option Constat) : Bool :=
  vue e || (match c with | some k => signalCPA k | none => false)

/-- **PR-57 (7) — l'enquête rend visible une contre-performativité que PR-54
    montre invisible**, dès qu'un constat CONTRAIRE recevable existe. -/
theorem l_enquete_rend_visible_la_contre_performativite (e : EcritureP) (k : Constat)
    (hc : contrePerformative e = true)
    (ho : e.declaree.operation ≠ .instrumentation)
    (hh : e.declaree.hote = .aucun ∨ e.declaree.hote = .nonRenseigne)
    (hk : signalCPA k = true) :
    vue e = false ∧ vueAvecEnquete e (some k) = true := by
  refine ⟨hors_hote_la_contre_performativite_est_invisible e hc ho hh, ?_⟩
  simp [vueAvecEnquete, hk]

/-- **PR-57 (8) — sans constat, rien ne change** : la lacune reste entière
    pour les cas non instruits. `[LECTURE — dépliage de `vueAvecEnquete`]`
    Témoin : `constat_temoin_discriminant`. -/
theorem sans_constat_la_lacune_demeure (e : EcritureP) :
    vueAvecEnquete e none = vue e := by
  simp [vueAvecEnquete]

/-! ## 5. Les déclencheurs -/

inductive Declencheur where
  | contestationConcernee | boucleConfirmante | refutationGoodhart | effetHote | echeance
  deriving DecidableEq, Repr

/-- Un déclencheur ouvre la phase ; l'échéance seulement si la revue associe
    les personnes concernées. -/
def ouvre (d : Declencheur) (concernesAssocies : Bool) : Bool :=
  match d with
  | .echeance => concernesAssocies
  | _ => true

/-- **PR-57 (9) — une échéance sans les concernés n'ouvre pas la phase** ;
    les quatre autres déclencheurs l'ouvrent. -/
theorem echeance_sans_concernes_n_ouvre_pas :
    ouvre .echeance false = false
  ∧ ∀ d, d ≠ .echeance → ∀ b, ouvre d b = true := by
  refine ⟨rfl, ?_⟩
  intro d hd b
  cases d <;> simp_all [ouvre]

end ProfRegPR57
