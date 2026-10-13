/-!
# PR-30 — Communalité (NT-ARCH §8.5.6) : branche B, règles A et B, arbitrage 6

28 septembre 2026. Décision du porteur (groupe C de l'audit du 26/09, lot C-β) :
verser les énoncés et les témoins proposés. **Premier ancrage formel de
§8.5.6** — aucun théorème compilé n'y portait jusqu'ici.

Ces théorèmes ancrent des **décisions déjà prises le 26/09** : branche B
(`creance_repartissable`, « `E+` qualifiant »), arbitrage 5 branche 2 (règles A
et B des formes d'affectation), arbitrage 6 (qualité pour inscrire le `D+`).
Ils établissent la **forme** de ces règles, jamais qu'une chose est un commun.

`[RÉSERVE DE MODÈLE]` Transcription de l'instructeur. Les valeurs du rejeu RATP
(témoin du capital d'apporteur) sont des **hypothèses déclarées** (H1-H3 du set).
Lean pur, sans import.
-/

namespace ProfRegPR30

/-! ## 1. C-2 reformulé — garde de la branche B (§8.5.6.2) -/

/-- `creance_repartissable` (§8.5, 26/09). -/
inductive Rep where
  | vrai | faux | nonDeterminable | nonDeclare
  deriving DecidableEq, Repr

inductive Qualif where
  | qualifie | nonQualifie | indetermine
  deriving DecidableEq, Repr

structure EngagementE where
  /-- `E+ ↔ ∅` avec `asymetrie_existentielle = VRAI` — condition (a). -/
  asymExistentielle : Bool
  repartissable     : Rep
  deriving DecidableEq, Repr

/-- « `E+` qualifiant » (règle amendée le 26/09). -/
def qualifiant (e : EngagementE) : Qualif :=
  if e.asymExistentielle then .qualifie else
  match e.repartissable with
  | .faux            => .qualifie
  | .vrai            => .nonQualifie
  | .nonDeterminable => .indetermine
  | .nonDeclare      => .nonQualifie

/-- `[ENGAGEMENT SANS QUALIFICATION DE RÉPARTISSABILITÉ]` — marqueur, jamais sanction. -/
def marqueurSansQualification (e : EngagementE) : Bool :=
  !e.asymExistentielle && e.repartissable == .nonDeclare

/-- Règle du 21/09 : tout `E+` satisfait la condition T — elle **échouait à exclure**. -/
def conditionT2109 (_ : EngagementE) : Bool := true

/-- **Garde de la branche B.** Le capital d'un apporteur (`creance_repartissable
    = VRAI`, hypothèse H1-H3 du rejeu RATP) n'était pas exclu par la règle du
    21/09 ; il ne qualifie pas sous la règle du 26/09. -/
theorem la_branche_B_exclut_le_capital_d_apporteur :
    conditionT2109 ⟨false, .vrai⟩ = true ∧ qualifiant ⟨false, .vrai⟩ = .nonQualifie := by
  decide

/-- **`NON_DETERMINABLE` : le calcul ne qualifie ni n'exclut.** -/
theorem non_determinable_rend_indetermine (e : EngagementE)
    (h₁ : e.asymExistentielle = false) (h₂ : e.repartissable = .nonDeterminable) :
    qualifiant e = .indetermine := by
  simp [qualifiant, h₁, h₂]

/-- **`NONDECLARE` ne qualifie pas, et marque** (patron CONV-9, RSO-8). -/
theorem le_non_declare_ne_qualifie_pas_et_marque (e : EngagementE)
    (h₁ : e.asymExistentielle = false) (h₂ : e.repartissable = .nonDeclare) :
    qualifiant e = .nonQualifie ∧ marqueurSansQualification e = true := by
  simp [qualifiant, marqueurSansQualification, h₁, h₂]

/-- **Témoin discriminant** : l'engagement existentiel qualifie sans déclaration
    de répartissabilité et sans marqueur ; un `E+` non répartissable qualifie. -/
theorem qualifiant_temoin_discriminant :
    qualifiant ⟨true, .nonDeclare⟩ = .qualifie
  ∧ marqueurSansQualification ⟨true, .nonDeclare⟩ = false
  ∧ qualifiant ⟨false, .faux⟩ = .qualifie := by
  decide

/-! ## 2. C-5 — règle A : la qualification se fait classe par classe (§8.5.6.2bis) -/

inductive Classe where
  | valeurEconomique | usage | prestation | autre
  deriving DecidableEq, Repr

/-- Règle A : la chose satisfait la condition T si **au moins une** classe porte
    `creance_repartissable = FAUX`. -/
def qualifieParClasse (cs : List (Classe × Rep)) : Bool :=
  cs.any (fun c => c.2 == .faux)

/-- Lecture agrégée écartée : « une classe répartissable suffit à répartir la chose ». -/
def qualifieAgrege (cs : List (Classe × Rep)) : Bool :=
  !(cs.any (fun c => c.2 == .vrai)) && cs.any (fun c => c.2 == .faux)

/-- **Une classe non répartissable suffit** (règle A). -/
theorem une_classe_non_repartissable_suffit (cs : List (Classe × Rep)) (c : Classe × Rep)
    (hc : c ∈ cs) (hf : c.2 = .faux) : qualifieParClasse cs = true := by
  unfold qualifieParClasse
  exact List.any_eq_true.mpr ⟨c, hc, by simp [hf]⟩

/-- **La qualification agrégée n'est pas la qualification par classe.** Fiducie :
    `USAGE` non répartissable, `VALEUR_ECONOMIQUE` répartissable — qualifie par
    classe, refusée par l'agrégat ; une valeur économique seule ne qualifie pas. -/
theorem la_qualification_agregee_n_est_pas_la_qualification_par_classe :
    qualifieParClasse [(.usage, .faux), (.valeurEconomique, .vrai)] = true
  ∧ qualifieAgrege [(.usage, .faux), (.valeurEconomique, .vrai)] = false
  ∧ qualifieParClasse [(.valeurEconomique, .vrai)] = false := by
  decide

/-! ## 3. C-13 — règle B : complétude des classes (fiducie) -/

/-- Classes attendues d'une fiducie (§8.5.6.2bis, tableau des conditions). -/
def attenduesFiducie : List Classe := [.usage, .valeurEconomique]

def completeFiducie (cs : List (Classe × Rep)) : Bool :=
  attenduesFiducie.all (fun k => cs.any (fun c => c.1 == k))

def statutFiducie (cs : List (Classe × Rep)) : Qualif :=
  if completeFiducie cs then (if qualifieParClasse cs then .qualifie else .nonQualifie)
  else .indetermine

/-- `[INSCRIPTION DE COMMUN INCOMPLÈTE — CLASSE DE CRÉANCE NON DÉCLARÉE]`. -/
def marqueurIncomplete (cs : List (Classe × Rep)) : Bool := !completeFiducie cs

/-- **Tant qu'une classe manque, `INDETERMINE`, et marqueur** — jamais `qualifie`. -/
theorem classe_manquante_rend_indetermine (cs : List (Classe × Rep))
    (h : completeFiducie cs = false) :
    statutFiducie cs = .indetermine ∧ marqueurIncomplete cs = true := by
  simp [statutFiducie, marqueurIncomplete, h]

/-- **La complétude prime sur la classe qualifiante** : l'usage non répartissable
    seul ne qualifie pas tant que la valeur économique n'est pas déclarée ;
    déclarée, la chose qualifie. -/
theorem la_completude_prime_sur_la_classe_qualifiante :
    statutFiducie [(.usage, .faux)] = .indetermine
  ∧ statutFiducie [(.usage, .faux), (.valeurEconomique, .vrai)] = .qualifie := by
  decide

/-! ## 4. C-4 — droit d'écrire ⇏ pouvoir d'engager (§8.5.6.5, arbitrage 6) -/

/-- `source_engagement_D` (§8.5, 26/09) ; `none` : légitimité `PRATIQUE` seule. -/
inductive SourceEngagement where
  | acteFormeAdmise | texteInstituant | reglesPropresCollectif
  deriving DecidableEq, Repr

structure DPlusCommun where
  source : Option SourceEngagement
  deriving DecidableEq, Repr

/-- Règle 3 : sans source, ce n'est pas un `D+` de commun. -/
def estDPlusDeCommun (d : DPlusCommun) : Bool := d.source.isSome

/-- `[HABILITATION NON ÉTABLIE — D+ SANS SOURCE D'ENGAGEMENT]` — marqueur. -/
def marqueurHabilitation (d : DPlusCommun) : Bool := d.source.isNone

/-- Règle 2 : un `D+` fondé sur les règles propres n'engage que le collectif.
    Les autres sources : portée fixée par l'acte ou le texte, **hors modèle** (`none`). -/
def engage (d : DPlusCommun) (membre : Bool) : Option Bool :=
  match d.source with
  | some .reglesPropresCollectif => some membre
  | some _                       => none
  | none                         => some false

/-- **Citer ses règles n'engage pas les tiers** (règle 2). -/
theorem citer_ses_regles_n_engage_pas_les_tiers (d : DPlusCommun)
    (h : d.source = some .reglesPropresCollectif) : engage d false = some false := by
  simp [engage, h]

/-- **La pratique seule marque, et ne fait pas un `D+` de commun** (règle 3). -/
theorem la_pratique_seule_marque_et_ne_qualifie_pas (d : DPlusCommun)
    (h : d.source = none) : estDPlusDeCommun d = false ∧ marqueurHabilitation d = true := by
  simp [estDPlusDeCommun, marqueurHabilitation, h]

/-- **Droit d'écrire ⇏ pouvoir d'engager** — témoin PLE Niayes (application K3
    du set) : inscriptible au titre de ses règles propres, sans marqueur ; engage
    ses membres, non les industriels. -/
theorem droit_d_ecrire_n_est_pas_pouvoir_d_engager :
    let d : DPlusCommun := ⟨some .reglesPropresCollectif⟩
    estDPlusDeCommun d = true ∧ marqueurHabilitation d = false
      ∧ engage d true = some true ∧ engage d false = some false := by
  decide

end ProfRegPR30
