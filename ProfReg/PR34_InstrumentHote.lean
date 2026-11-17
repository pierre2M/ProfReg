import ProfReg.PR33_EffetDuDefaut
/-!
# PR-34 — L'instrument-hôte (P5, NT-ARCH §B.2bis.3)

28 septembre 2026. Décision du porteur : verser P5 en Lean (écarté du groupe C
sur une prémisse inexacte), avec l'effet du défaut décidé le même jour —
**E3 en principe** (un hôte non déclaré laisse ignorer s'il gouverne ; RSO-8),
**E4** si le triplet est incomplet mais que son point 3 déclare explicitement
qu'aucune gouvernance n'est imposée ; **réfutée**, cette déclaration ramène en E3.

`[RÉSERVE DE MODÈLE]` Le point 3 du triplet (« ce que l'hôte impose ») est
réduit ici à sa part de gouvernance ; forme et calendrier ne sont pas modélisés.
Identités codées par `Nat`. Le signal `INSTRUMENT_HOTE_NON_DECLARE` et le
marqueur `[INSTRUMENT HÔTE INCOMPLET]` sont les marqueurs **du registre** ; le
`[DÉCOUPLAGE DE RÉGIMES]` épistémique est retiré de l'effet (piste 5).
-/

namespace ProfRegPR34

open ProfRegPR33

inductive OperationInstituante where
  | problematisation | instrumentation | legitimation | aucune | nonInstruit
  deriving DecidableEq, Repr

inductive Gouvernance where
  | imposee | aucuneImposee
  deriving DecidableEq, Repr

structure Triplet where
  dispositif  : Option Nat
  concepteur  : Option Nat
  gouvernance : Option Gouvernance   -- point 3, part de gouvernance
  deriving DecidableEq, Repr

inductive Hote where
  | nonRenseigne | aucun | declare (t : Triplet)
  deriving DecidableEq, Repr

structure EcritureInstituee where
  operation : OperationInstituante
  hote      : Hote
  /-- La déclaration « aucune gouvernance imposée » a été réfutée par un tiers. -/
  refutee   : Bool
  deriving DecidableEq, Repr

def complet (t : Triplet) : Bool :=
  t.dispositif.isSome && t.concepteur.isSome && t.gouvernance.isSome

/-- Effet du défaut de P5 ; `none` : pas de défaut. -/
def effetP5 (e : EcritureInstituee) : Option Effet :=
  if e.operation == .instrumentation then
    match e.hote with
    | .declare t =>
      if complet t then none
      else if t.gouvernance == some .aucuneImposee && !e.refutee then some .E4
      else some .E3
    | _ => some .E3
  else none

/-- **Hôte non renseigné, ou `AUCUN` sous `INSTRUMENTATION` : E3, DÉLIBÉRATION.** -/
theorem hote_non_declare_delibere (e : EcritureInstituee)
    (h₁ : e.operation = .instrumentation)
    (h₂ : e.hote = .nonRenseigne ∨ e.hote = .aucun) : effetP5 e = some .E3 := by
  rcases h₂ with h | h <;> simp [effetP5, h₁, h]

/-- **La voie intermédiaire ne dispense pas du triplet** : un triplet incomplet
    reste un défaut, quelle que soit la déclaration de gouvernance. -/
theorem la_voie_intermediaire_ne_dispense_pas_du_triplet (e : EcritureInstituee) (t : Triplet)
    (h₁ : e.operation = .instrumentation) (h₂ : e.hote = .declare t)
    (h₃ : complet t = false) : (effetP5 e).isSome = true := by
  simp only [effetP5, h₁, h₂, h₃]
  split
  · split
    · simp_all
    · split <;> rfl
  · simp_all

/-- **Témoin discriminant** : triplet complet, pas de défaut ; hôte non renseigné, E3. -/
theorem P5_temoin_discriminant :
    effetP5 ⟨.instrumentation, .declare ⟨some 1, some 2, some .imposee⟩, false⟩ = none
  ∧ effetP5 ⟨.instrumentation, .nonRenseigne, false⟩ = some .E3 := by
  decide

/-- **L'exception, et sa réfutation** : incomplet avec « aucune gouvernance
    imposée » → E4 ; la même déclaration réfutée → E3 ; gouvernance imposée → E3. -/
theorem sans_gouvernance_declaree_le_marqueur_suffit :
    effetP5 ⟨.instrumentation, .declare ⟨some 1, none, some .aucuneImposee⟩, false⟩ = some .E4
  ∧ effetP5 ⟨.instrumentation, .declare ⟨some 1, none, some .aucuneImposee⟩, true⟩ = some .E3
  ∧ effetP5 ⟨.instrumentation, .declare ⟨some 1, none, some .imposee⟩, false⟩ = some .E3 := by
  decide

/-- **P5 suit le critère** : ses deux effets coïncident avec le classement des
    défauts `p5Principe` et `p5Exception` (PR-33). -/
theorem P5_suit_le_critere :
    effetP5 ⟨.instrumentation, .nonRenseigne, false⟩ = some (classer p5Principe)
  ∧ effetP5 ⟨.instrumentation, .declare ⟨some 1, none, some .aucuneImposee⟩, false⟩
      = some (classer p5Exception) := by
  decide

end ProfRegPR34
