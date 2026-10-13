/-
  PR-46 · Le registre de chaîne : la relation à trois parties (D-ED-18)
  ====================================================================

  Porteur : Pierre Musseau. Écrit le 30 septembre 2026, sur instruction de
  D-ED-18. Note : `Note_D-ED-18_Chaine_de_Valeur_Registre_de_Chaine_2026-09-30.md`.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR45_ProtocoleAttestationEtMiroirReconstitue`.

  LE PROBLÈME (note des cinq situations, S3)
  ------------------------------------------
  La vigilance vise des atteintes aux TIERS (travailleurs, riverains,
  consommateurs, milieu), non au fournisseur : la relation est à trois
  parties ; l'écriture duale (PR-35) est binaire.

  L'INTUITION DU PORTEUR, ET SON ANCRAGE
  --------------------------------------
  Une gouvernance organisée À L'ÉCHELLE DE LA CHAÎNE tient un registre de
  communalité ; les entreprises qui exercent leur vigilance l'alimentent
  par écritures duales. Ancrage : Accord sur la sécurité incendie et la
  sécurité des bâtiments au Bangladesh (13 mai 2013) — comité de pilotage
  paritaire à présidence OIT (§4), inspecteur indépendant (§8), liste
  unique agrégée des fournisseurs (§19a), plaintes (§18), financement par
  les signataires (§24), arbitrage contraignant (§5).

  LA RÈGLE FORMALISÉE
  -------------------
  1. ÉTOILE, NON TRIANGLE : chaque entreprise est en écriture duale avec le
     REGISTRE DE CHAÎNE (binaire, PR-35) ; l'entreprise et le fournisseur
     n'ont pas à s'écrire en communalité.
  2. LA TROISIÈME ARITÉ SUBSISTE comme ANNOTATION de l'engagement (site
     fournisseur, objet préservé) : la projection en ligne duale la perd
     (même garde que PR-29 et PR-23 §6).
  3. QUALIFICATION PAR LE LIEN (OCDE 2023, I.A.12-13, commentaires 21-23 ;
     CS3D art. 10 §1 a)) : une réparation n'est une DETTE que si
     l'entreprise CAUSE ou CONTRIBUE ; si elle est seulement DIRECTEMENT
     LIÉE, c'est une participation volontaire — « Ceci ne doit pas être
     interprété comme transférant la responsabilité de l'entité à l'origine
     d'un impact négatif » (OCDE 2023, I.A.13) [D-ED-37 — 30/09/2026].
  4. OBJETS DÉCLARÉS : le registre de chaîne ne reçoit que les engagements
     portant sur ses objets (l'Accord : santé-sécurité, incendie et bâtiment).
  5. PLAINTE FONDÉE = MIROIR FORCÉ : « lorsque la plainte est fondée,
     l'incidence négative … [est] réputée recensée » (CS3D art. 14 §3) :
     l'entreprise complète son registre (PR-35 `completer`).
     [D-ED-37 — 30/09/2026] Précisé par D-ED-30 (PR-48) : l'avis « fondée » de la
     société vaut RECONNAISSANCE ; à défaut, le miroir est forcé par une
     plainte RETENUE par l'instance commune ou l'autorité de supervision
     (`plainte_retenue_miroir_force`).
  6. CONSENTEMENT EX ANTE : l'entreprise signataire a consenti d'avance à
     l'ARBITRAGE (Accord §5) ; son refus ultérieur ne le ferme pas. Il ne
     vaut pas pour la TRANSACTION, dont le consentement se donne sur
     l'issue (art. 2044 C. civ.). [D-ED-29 — 30/09/2026 : correction ;
     la version initiale rabattait l'arbitrage sur la transaction.]
  7. TENEUR ≠ INSTANCE : si le comité de pilotage tient le registre, il ne
     peut en être l'instance de contrôle (PR-43) ; l'inspecteur
     indépendant, désigné par les deux registres, le peut.

  CE QUE LE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne détermine pas le lien (cause / contribue / directement lié) :
    déclaré. C'est le point le plus disputable (OCDE, comm. 16 : « la
    relation … n'est toutefois pas figée ») ; sa QUALIFICATION par
    l'instance commune est l'objet de PR-47 (CONV-18) [D-ED-37 — 30/09/2026].
  · ~~Il ne modélise pas l'arbitrage comme voie distincte~~ : voie
    `arbitrage` ajoutée à PR-44 (D-ED-29).
  · D-ED-26 (30/09/2026) : l'étoile est RETENUE comme réponse à D-ED-18
    (C6 close). D-ED-27 : l'annotation de destination est l'objet de
    CONV-18 (PR-47).
  · Il ne dit pas qui, parmi les concernés, écrit (PR-37 s'applique).
-/

import ProfReg.PR45_ProtocoleAttestationEtMiroirReconstitue

namespace ProfRegPR46

open ProfRegPR35 (Entite Ligne Registre EcritureDuale ecart completer lignesVers aSonMiroir estMiroir)
open ProfRegPR43 (DesignationControle instanceCommune)
open ProfRegPR44 (Saisine Qualite saisineRecevable)

/-! ## 1. Lien, objet, engagement -/

/-- Le lien de l'entreprise à l'incidence (OCDE 2023, I.A.12-13). -/
inductive Lien where
  | cause
  | contribue       -- « contribution substantielle » (OCDE, comm. 16)
  | directementLie  -- par une relation d'affaires, sans cause ni contribution
  deriving DecidableEq, Repr

/-- Ce que la gouvernance de chaîne préserve. -/
inductive Objet where
  | santeSecurite
  | communauteLocale
  | consommateur
  | environnement
  deriving DecidableEq, Repr

inductive NatureEngagement where
  | financement        -- Accord §24
  | maintienCommandes  -- Accord §23
  | correctionExigee   -- Accord §12, §21 : exiger du fournisseur
  | reparation
  deriving DecidableEq, Repr

inductive Qualification where
  | dette
  | participationVolontaire
  | exigenceDInfluence
  deriving DecidableEq, Repr

/-- **Règle 3.** -/
def qualifier : Lien → NatureEngagement → Qualification
  | _,               .financement       => .dette
  | _,               .maintienCommandes => .dette
  | _,               .correctionExigee  => .exigenceDInfluence
  | .cause,          .reparation        => .dette
  | .contribue,      .reparation        => .dette
  | .directementLie, .reparation        => .participationVolontaire

structure EngagementVigilance where
  entreprise : Entite
  fournisseur : Entite   -- le site : troisième arité
  objet      : Objet     -- ce qui est préservé
  lien       : Lien
  nature     : NatureEngagement
  montant    : Nat
  deriving DecidableEq, Repr

/-! ## 2. Le registre de chaîne et les registres des entreprises -/

/-- Les dettes de l'entreprise `b` envers le registre de chaîne `r`
    (seules les dettes entrent dans l'écriture duale). -/
def lignesEntreprise (r b : Entite) (es : List EngagementVigilance) : List (Ligne Nat) :=
  es.filterMap (fun e =>
    if e.entreprise == b && decide (qualifier e.lien e.nature = .dette)
    then some ⟨r, .Dplus, e.montant⟩ else none)

/-- Le registre de chaîne porte le miroir de chaque dette. -/
def lignesChaine (es : List EngagementVigilance) : List (Ligne Nat) :=
  es.filterMap (fun e =>
    if decide (qualifier e.lien e.nature = .dette)
    then some ⟨e.entreprise, .Cplus, e.montant⟩ else none)

/-- **Règle 4.** Seuls les engagements sur un objet déclaré sont reçus. -/
def recus (objets : List Objet) (es : List EngagementVigilance) : List EngagementVigilance :=
  es.filter (fun e => objets.contains e.objet)

def registreChaine (r : Entite) (objets : List Objet) (es : List EngagementVigilance) :
    Registre Nat := ⟨r, lignesChaine (recus objets es)⟩

def registreEntreprise (r b : Entite) (objets : List Objet) (es : List EngagementVigilance) :
    Registre Nat := ⟨b, lignesEntreprise r b (recus objets es)⟩

/-! ## 3. Ce qui se démontre (général) -/

/-- **Règle 3 — directement lié, la réparation n'est jamais une dette**
    (OCDE 2023, comm. 23 : la responsabilité n'est pas transférée). -/
theorem directement_lie_pas_de_dette_de_reparation :
    qualifier .directementLie .reparation = .participationVolontaire := rfl

/-- **Règle 3 — exiger une correction n'endette pas** : c'est l'usage de
    l'influence (OCDE, comm. 22-23), quel que soit le lien. -/
theorem exiger_n_endette_pas (l : Lien) :
    qualifier l .correctionExigee = .exigenceDInfluence := by
  cases l <;> rfl

/-- **Règle 2 — la projection perd le site fournisseur** : deux
    engagements qui ne diffèrent que par le fournisseur donnent la même
    ligne duale. La troisième arité n'est portée que par l'annotation. -/
theorem la_projection_perd_le_fournisseur (r : Entite) (e : EngagementVigilance) (f : Entite) :
    lignesEntreprise r e.entreprise [e]
      = lignesEntreprise r e.entreprise [{ e with fournisseur := f }] := rfl

/-- **Règle 5 — plainte fondée, miroir forcé.** Si la plainte est fondée,
    l'entreprise complète son registre : l'écart du registre de chaîne
    envers elle disparaît (PR-35). -/
def recenserSiFondee (fondee : Bool) (RB R : Registre Nat) : Registre Nat :=
  if fondee then completer RB R else RB

theorem plainte_fondee_ecart_resorbe (RB R : Registre Nat) :
    ecart R (recenserSiFondee true RB R) = [] :=
  ProfRegPR35.le_rapprochement_resorbe_l_ecart R RB

/-- **Règle 6 — le consentement ex ante** : la signature vaut consentement
    pour l'arbitrage seulement. -/
def consentPour (v : ProfRegPR44.Voie) (signataire consentActuel : Bool) : Bool :=
  match v with
  | .arbitrage => signataire || consentActuel
  | _          => consentActuel

theorem la_signature_vaut_consentement_ex_ante (q : Qualite) (i : Option Bool) (c : Bool) :
    saisineRecevable ⟨.arbitrage, q, consentPour .arbitrage true c, i⟩ = true := rfl

/-- **Règle 6 — mais pas pour la transaction** : le signataire qui refuse
    au moment de transiger ferme la transaction ; l'arbitrage reste ouvert. -/
theorem la_signature_n_ouvre_pas_la_transaction (q : Qualite) (i : Option Bool) :
    saisineRecevable ⟨.transaction, q, consentPour .transaction true false, i⟩ = false
    ∧ saisineRecevable ⟨.arbitrage, q, consentPour .arbitrage true false, i⟩ = true := ⟨rfl, rfl⟩

/-- **L'étoile, forme générale** `[D-ED-37 — 30/09/2026]` : pour tout
    teneur de chaîne `r`, toute entreprise `b`, tous objets et tous
    engagements, le registre de l'entreprise et le registre de chaîne sont
    en écriture duale (PR-35). L'instance du §4 n'en est qu'un témoin. -/
theorem l_etoile_est_toujours_duale (r b : Entite) (objets : List Objet)
    (es : List EngagementVigilance) :
    EcritureDuale (registreEntreprise r b objets es) (registreChaine r objets es) := by
  constructor
  · unfold ecart
    apply ProfRegPR35.filtre_vide_de_tous_faux
    intro l hl
    unfold lignesVers at hl
    rw [List.mem_filter] at hl
    obtain ⟨hl, -⟩ := hl
    simp only [registreEntreprise, lignesEntreprise, List.mem_filterMap] at hl
    obtain ⟨e, he, hsome⟩ := hl
    split at hsome
    · rename_i hc
      cases hsome
      rw [Bool.and_eq_true] at hc
      obtain ⟨hb, hq⟩ := hc
      unfold aSonMiroir
      simp only [Bool.not_eq_false']
      rw [List.any_eq_true]
      refine ⟨⟨e.entreprise, .Cplus, e.montant⟩, ?_, ?_⟩
      · simp only [registreChaine, lignesChaine, List.mem_filterMap]
        exact ⟨e, he, by rw [if_pos hq]⟩
      · unfold estMiroir
        show (e.entreprise == b && (ProfRegPR20.TypageIA.Cplus == ProfRegPR20.miroirIA .Dplus)) = true
        rw [hb]; rfl
    · cases hsome
  · unfold ecart
    apply ProfRegPR35.filtre_vide_de_tous_faux
    intro l hl
    unfold lignesVers at hl
    rw [List.mem_filter] at hl
    obtain ⟨hl, hc⟩ := hl
    simp only [registreChaine, lignesChaine, List.mem_filterMap] at hl
    obtain ⟨e, he, hsome⟩ := hl
    split at hsome
    · rename_i hq
      cases hsome
      unfold aSonMiroir
      simp only [Bool.not_eq_false']
      rw [List.any_eq_true]
      have hb : (e.entreprise == b) = true := hc
      refine ⟨⟨r, .Dplus, e.montant⟩, ?_, ?_⟩
      · simp only [registreEntreprise, lignesEntreprise, List.mem_filterMap]
        refine ⟨e, he, ?_⟩
        rw [if_pos]
        rw [Bool.and_eq_true]; exact ⟨hb, hq⟩
      · unfold estMiroir
        show ((r == r) && (ProfRegPR20.TypageIA.Dplus == ProfRegPR20.miroirIA .Cplus)) = true
        rw [show (r == r) = true from decide_eq_true rfl]; rfl
    · cases hsome

/-! ## 4. Instance : l'Accord, stylisé -/

def marque1 : Entite := 100
def marque2 : Entite := 101
def usine   : Entite := 200
def comitePilotage : Entite := 300   -- teneur du registre de chaîne (Accord §4)
def inspecteur     : Entite := 311   -- indépendant (Accord §8)

def objetsAccord : List Objet := [.santeSecurite]

def engagements : List EngagementVigilance :=
  [ ⟨marque1, usine, .santeSecurite, .directementLie, .financement, 50⟩
  , ⟨marque1, usine, .santeSecurite, .directementLie, .correctionExigee, 0⟩
  , ⟨marque2, usine, .santeSecurite, .contribue, .reparation, 30⟩
  , ⟨marque2, usine, .santeSecurite, .directementLie, .maintienCommandes, 20⟩
  , ⟨marque1, usine, .environnement, .cause, .reparation, 99⟩ ]   -- hors objet

def regChaine : Registre Nat := registreChaine comitePilotage objetsAccord engagements
def regM1 : Registre Nat := registreEntreprise comitePilotage marque1 objetsAccord engagements
def regM2 : Registre Nat := registreEntreprise comitePilotage marque2 objetsAccord engagements

/-- **PR-46 (1) — l'étoile.** Chaque marque est en écriture duale avec le
    registre de chaîne ; la même usine est couverte par les deux. -/
theorem l_etoile_porte_la_chaine :
    EcritureDuale regM1 regChaine ∧ EcritureDuale regM2 regChaine := by
  decide

/-- **PR-46 (2) — l'objet déclaré borne le registre** : l'engagement
    « environnement » (99) n'entre pas dans le registre de l'Accord. -/
theorem l_objet_declare_borne_le_registre :
    regM1.lignes = [⟨comitePilotage, .Dplus, 50⟩]
    ∧ regChaine.lignes = [⟨marque1, .Cplus, 50⟩, ⟨marque2, .Cplus, 30⟩, ⟨marque2, .Cplus, 20⟩] := by
  decide

/-- **PR-46 (3) — pas de consolidation** : les dettes restent par marque. -/
theorem pas_de_consolidation_dans_la_chaine :
    ProfRegPR35.lignesVers regChaine regM1 = [⟨marque1, .Cplus, 50⟩]
    ∧ ProfRegPR35.lignesVers regChaine regM2 = [⟨marque2, .Cplus, 30⟩, ⟨marque2, .Cplus, 20⟩] := by
  decide

/-- **PR-46 (4) — teneur ≠ instance** : l'inspecteur désigné par la marque
    et par le registre de chaîne est l'instance commune ; le comité de
    pilotage, teneur, ne l'est pas (PR-43). -/
def dsChaine : List DesignationControle :=
  [ ⟨marque1, inspecteur, .arretee⟩, ⟨comitePilotage, inspecteur, .arretee⟩
  , ⟨marque1, comitePilotage, .arretee⟩, ⟨comitePilotage, comitePilotage, .arretee⟩ ]

theorem le_teneur_n_est_pas_l_instance :
    instanceCommune dsChaine marque1 comitePilotage inspecteur = true
    ∧ instanceCommune dsChaine marque1 comitePilotage comitePilotage = false := by
  decide

/-- **PR-46 (5) — la plainte fondée force le miroir** : la marque 1 n'a
    pas inscrit une dette de réparation que le registre de chaîne porte
    envers elle ; plainte fondée → écart résorbé ; non fondée → l'écart
    reste. -/
def regChainePlainte : Registre Nat := ⟨comitePilotage, [⟨marque1, .Cplus, 40⟩]⟩
def regM1Vide : Registre Nat := ⟨marque1, []⟩

theorem la_plainte_fondee_force_le_miroir :
    ecart regChainePlainte (recenserSiFondee true regM1Vide regChainePlainte) = []
    ∧ ecart regChainePlainte (recenserSiFondee false regM1Vide regChainePlainte)
        = [⟨marque1, .Cplus, 40⟩] := by
  decide

/-- **Témoin discriminant** (R-7) de `qualifier` et du consentement ex ante. -/
theorem qualifier_temoin_discriminant :
    qualifier .cause .reparation = .dette
    ∧ qualifier .contribue .reparation = .dette
    ∧ qualifier .directementLie .reparation = .participationVolontaire
    ∧ saisineRecevable ⟨.arbitrage, .quelconque, consentPour .arbitrage true false, none⟩ = true
    ∧ saisineRecevable ⟨.arbitrage, .quelconque, consentPour .arbitrage false false, none⟩ = false := by
  decide

end ProfRegPR46
