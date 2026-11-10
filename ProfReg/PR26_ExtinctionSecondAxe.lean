/-
  ProfReg — PR-26 — Le second axe d'extinction
  [VERSÉ AU PROGRAMME LE 28/09/2026 — décision de porteur D-12]
  =====================================================================================
  Source : NT-ARCH §4bis (décision de porteur du 21 septembre 2026 ; A-T-7 et A-T-8
  du 26 septembre 2026). Audit du 26 septembre 2026.

  STATUT. Écrit le 26/09 comme proposition ; **versé le 28/09 (D-12)**. Le second axe
  reste procédural pour tout ce que ce modèle ne couvre pas (la trace, §4bis.5 ; la
  qualité des interprètes) ; ce fichier en formalise les **conditions de bonne
  formation** et les **non-implications**. Complété le 28/09 par la règle D-9b
  (une dette AX-2 ne s'inscrit jamais en `ETEINTE`).

  Ce que le fichier établit (classe ProfReg : bonne formation et non-implications) :
    (1) le silence ne solde rien — `NONDECLARE` n'est jamais une extinction ;
    (2) la lecture paresseuse du quart lemme est refusée : deux prises contraires,
        chacune avec interprète et régime, ne suffisent pas sans le tiers lemme (4 → 3) ;
    (3) l'axe est orthogonal à la trajectoire d'attribution (`StatutDette` de V4,
        importé et NON modifié) — c'est la garde de NT-ARCH §4bis.2, rendue calculable ;
    (4) l'extinction par le seul débiteur est bien formée ET marquée : marqueur, jamais
        sanction (R0-bis) ;
    (5) une extinction bien formée n'exige pas une réalisation vérifiée — ce qui est
        cohérent avec PR-11 depuis D-9a (28/09) : NC porte sur l'extinction par exécution ;
    (7) [D-9b, 28/09] une dette AX-2 ne s'inscrit jamais en `ETEINTE`, et le quart lemme
        lui reste ouvert.

  Ce que le fichier n'établit pas : ni que les valeurs 3 et 4 prouvent une logique non
  bivalente (A-T-8 : homologues mondains), ni qu'une extinction est juste, ni que la
  trace demeure (§4bis.5, hors modèle).

  Lean 4, sans Mathlib. Aucune égalité de `String` n'est décidée par `simp`.
-/
import ProfReg.Primitives

namespace ProfRegPR26

open ProfReg

/-! ## 1. Le modèle -/

/-- Les quatre lemmes (ordre de Yamauchi) et le hors-tétralemme. -/
inductive EtatExtinction where
  | eteinte                -- lemme 1
  | nonEteinte             -- lemme 2
  | indecidableAtteste     -- lemme 3 — homologue mondain (A-T-8)
  | eteinteEtNonEteinte    -- lemme 4 — pluralité de rapports déclarée
  | nonDeclare             -- hors tétralemme : refuse, n'autorise pas
  deriving DecidableEq, Repr

/-- Le mode par lequel ce qui était dû cesse de l'être (§4bis.2 : « remise,
    prescription, disparition de l'objet » à côté de l'exécution). -/
inductive ModeExtinction where
  | realisationVerifiee
  | remise
  | prescription
  | disparitionObjet
  deriving DecidableEq, Repr

/-- Une prise d'interprète : qui constate, sous quel régime. `none` = non renseigné. -/
structure Prise where
  interprete : Option String
  regime     : Option String
  deriving Repr

/-- Une inscription sur l'axe d'extinction d'une obligation. -/
structure Inscription where
  obligation        : Nat
  statutAttribution : StatutDette            -- axe de §4, importé, inchangé
  etat              : EtatExtinction
  prises            : List Prise              -- lemmes 1 et 2 : une ; lemme 4 : deux
  critereResolution : Option String           -- exigé au lemme 3
  ecritureAppariee  : Bool                    -- lemme 1 : écriture §8.5.2 (ex. D− ↔ C− + e)
  mode              : Option ModeExtinction
  declareNonDecidableSousRegimeUnique : Bool  -- seconde branche de la dépendance 4 → 3
  interpreteEstSeulDebiteur : Bool
  concernesTiennentLeMiroir : Bool
  /-- [D-9b, 28/09] L'obligation relève du régime **AX-2** (héritée, renouvelée,
      sans créancier apte à donner quittance ; PR-12 `Regime.A2`). -/
  regimeA2 : Bool
  deriving Repr

def priseRenseignee (p : Prise) : Bool := p.interprete.isSome && p.regime.isSome

/-- Le lemme 3 a-t-il été attesté sur la même obligation, dans l'historique ? -/
def tiersAtteste (hist : List Inscription) (o : Nat) : Bool :=
  hist.any (fun i => i.obligation == o && i.etat == EtatExtinction.indecidableAtteste)

/-- **Bonne formation**, table de §4bis.3, lue sur l'inscription et son historique. -/
def BienFormee (hist : List Inscription) (i : Inscription) : Bool :=
  match i.etat with
  | EtatExtinction.eteinte =>
      i.ecritureAppariee && (i.prises.any priseRenseignee) && !i.regimeA2
  | EtatExtinction.nonEteinte =>
      i.prises.any (fun p => p.interprete.isSome)
  | EtatExtinction.indecidableAtteste =>
      i.prises.any (fun p => p.interprete.isSome) && i.critereResolution.isSome
  | EtatExtinction.eteinteEtNonEteinte =>
      decide (2 ≤ (i.prises.filter priseRenseignee).length)
        && (tiersAtteste hist i.obligation || i.declareNonDecidableSousRegimeUnique)
  | EtatExtinction.nonDeclare => true    -- état du registre, toujours inscriptible

/-- Ce que le registre compte comme éteint : le seul lemme 1. -/
def compteEteinte (i : Inscription) : Bool := i.etat == EtatExtinction.eteinte

/-- Marqueur A-T-7 : `[EXTINCTION DÉCLARÉE PAR LE SEUL DÉBITEUR]`. -/
def marqueurSeulDebiteur (i : Inscription) : Bool :=
  i.etat == EtatExtinction.eteinte
    && i.statutAttribution == StatutDette.attribuee
    && i.interpreteEstSeulDebiteur
    && !i.concernesTiennentLeMiroir

/-! ## 2. Témoins -/

def priseA : Prise := { interprete := some "interprete-1", regime := some "CARE" }
def priseB : Prise := { interprete := some "interprete-2", regime := some "PCG" }

def base : Inscription :=
  { obligation := 1, statutAttribution := StatutDette.attribuee
  , etat := EtatExtinction.nonDeclare, prises := [], critereResolution := none
  , ecritureAppariee := false, mode := none
  , declareNonDecidableSousRegimeUnique := false
  , interpreteEstSeulDebiteur := false, concernesTiennentLeMiroir := false
  , regimeA2 := false }

/-! ## 3. Théorèmes -/

/-- **(1) Le silence ne solde rien.** Quel que soit l'historique, une inscription
    `nonDeclare` est inscriptible et ne compte jamais comme extinction. -/
theorem le_silence_ne_solde_rien (hist : List Inscription) (i : Inscription)
    (h : i.etat = EtatExtinction.nonDeclare) :
    BienFormee hist i = true ∧ compteEteinte i = false := by
  simp [BienFormee, compteEteinte, h]

/-- **(2) La lecture paresseuse du quart lemme est refusée.** Il existe une inscription
    au lemme 4 portant deux prises contraires complètes (interprète et régime chacune),
    qui n'est pas bien formée : sans tiers lemme attesté ni déclaration de
    non-décidabilité sous régime unique, « deux régimes divergent » ne suffit pas. -/
theorem deux_regimes_divergents_ne_suffisent_pas :
    ∃ i : Inscription,
      i.etat = EtatExtinction.eteinteEtNonEteinte
      ∧ (i.prises.filter priseRenseignee).length = 2
      ∧ BienFormee [] i = false :=
  ⟨{ base with etat := EtatExtinction.eteinteEtNonEteinte, prises := [priseA, priseB] },
   rfl, by decide, by decide⟩

/-- **(2′) … et le tiers lemme attesté suffit à la rendre bien formée.** La dépendance
    4 → 3 est donc une condition effective, non décorative. -/
theorem le_tiers_atteste_leve_le_refus :
    ∃ (h : Inscription) (i : Inscription),
      h.etat = EtatExtinction.indecidableAtteste
      ∧ BienFormee [] h = true
      ∧ i.etat = EtatExtinction.eteinteEtNonEteinte
      ∧ BienFormee [h] i = true :=
  ⟨{ base with etat := EtatExtinction.indecidableAtteste, prises := [priseA]
             , critereResolution := some "constat de terrain des concernés" },
   { base with etat := EtatExtinction.eteinteEtNonEteinte, prises := [priseA, priseB] },
   rfl, by decide, rfl, by decide⟩

/-- **(3) L'axe d'extinction est orthogonal à la trajectoire d'attribution.**
    Une obligation **non attribuée** peut être éteinte de façon bien formée (remise),
    et une obligation **attribuée** peut rester non éteinte. `StatutDette` et
    `transition_valide` sont importés de `Primitives.lean` sans modification :
    c'est la garde de NT-ARCH §4bis.2, vérifiée par compilation. -/
theorem l_extinction_ne_depend_pas_de_l_attribution :
    (∃ i : Inscription, i.statutAttribution = StatutDette.nonAttribuee
        ∧ BienFormee [] i = true ∧ compteEteinte i = true)
    ∧ (∃ i : Inscription, i.statutAttribution = StatutDette.attribuee
        ∧ BienFormee [] i = true ∧ compteEteinte i = false) :=
  ⟨⟨{ base with statutAttribution := StatutDette.nonAttribuee
              , etat := EtatExtinction.eteinte, prises := [priseA]
              , ecritureAppariee := true, mode := some ModeExtinction.remise },
    rfl, by decide, by decide⟩,
   ⟨{ base with etat := EtatExtinction.nonEteinte, prises := [priseA] },
    rfl, by decide, by decide⟩⟩

/-- **(3′) La machine de §4 n'est pas touchée** : l'extinction ne change rien à la
    règle d'accès au niveau CRITIQUE. `[GARDE DE NON-RÉGRESSION — VRAIE PAR
    CONSTRUCTION, DÉCLARÉE]` (NT-ARCH §8ter-bis, R-5) ; artefacts gardés : le champ
    `statutAttribution` de PR-26 et `transition_valide` (V4). Énoncé volontairement minimal — il est vrai par
    construction (aucun terme de l'axe d'extinction n'entre dans `transition_valide`) ;
    son rôle est d'échouer à compiler si une révision future les couplait. -/
theorem la_machine_d_attribution_ignore_l_extinction (i : Inscription)
    (h : i.statutAttribution = StatutDette.nonAttribuee) :
    ¬ transition_valide i.statutAttribution NiveauRIA.critique := by
  rw [h]; exact id

/-- **(4) Seul débiteur : bien formée et marquée.** Le marqueur n'est pas un refus. -/
theorem seul_debiteur_bien_forme_mais_marque :
    ∃ i : Inscription, BienFormee [] i = true ∧ marqueurSeulDebiteur i = true
      ∧ compteEteinte i = true :=
  ⟨{ base with etat := EtatExtinction.eteinte, prises := [priseA]
             , ecritureAppariee := true, mode := some ModeExtinction.realisationVerifiee
             , interpreteEstSeulDebiteur := true },
   by decide, by decide, by decide⟩

/-- **(4′) Le miroir tenu par les concernés lève le marqueur**, sans rien changer à la
    bonne formation.

    `[LECTURE — D-13]` Dépliage de `marqueurSeulDebiteur`, licite (R-2) : le
    marqueur est levé par `seul_debiteur_bien_forme_mais_marque`. Ce n'est pas une
    garde : une seule définition y intervient (R-5 v). -/
theorem le_miroir_des_concernes_leve_le_marqueur (i : Inscription)
    (h : i.concernesTiennentLeMiroir = true) : marqueurSeulDebiteur i = false := by
  simp [marqueurSeulDebiteur, h]

/-- **(5) Une extinction bien formée n'exige pas une réalisation vérifiée.**
    C'est ce que §4bis.2 admet (remise, prescription) — et ce que PR-11
    `seule_la_realisation_eteint` exclut dans son propre modèle. Les deux fichiers
    compilent ensemble : ils ne se contredisent pas **en Lean**, ils modélisent deux
    règles différentes sous le même mot. ~~`[INCOHÉRENCE INTER-DOCUMENTS — niveau 2]`~~
    [D-9a, 28/09 — tranché par le porteur : NC porte sur l'extinction **par exécution** ;
    la remise relève du second axe. Ce théorème en est désormais l'appui, non l'objection.] -/
theorem une_extinction_bien_formee_peut_etre_une_remise :
    ∃ i : Inscription, BienFormee [] i = true ∧ compteEteinte i = true
      ∧ i.mode = some ModeExtinction.remise :=
  ⟨{ base with etat := EtatExtinction.eteinte, prises := [priseA]
             , ecritureAppariee := true, mode := some ModeExtinction.remise },
   by decide, by decide, rfl⟩

/-- **(6) Le tiers lemme exige un critère de résolution** (la cruche « pas maintenant
    dans la maison » : on dit à quelle condition on ira en chercher une). -/
theorem tiers_lemme_sans_critere_mal_forme :
    ∃ i : Inscription, i.etat = EtatExtinction.indecidableAtteste
      ∧ i.prises.any (fun p => p.interprete.isSome) = true
      ∧ BienFormee [] i = false :=
  ⟨{ base with etat := EtatExtinction.indecidableAtteste, prises := [priseA] },
   rfl, by decide, by decide⟩

/-! ## 4. La règle D-9b — AX-2 et le second axe (28/09/2026) -/

/-- **(7) Une dette AX-2 ne s'inscrit jamais en `ETEINTE`.** Quel que soit
    l'historique, et même avec une écriture appariée et une prise complète :
    ce qu'AX-2 pose comme non soldable ne se solde pas par une inscription.
    (NT-ARCH §4bis.3, règle D-9b ; condition de réfutation (iii) de §4bis.7.) -/
theorem une_dette_A2_ne_s_eteint_jamais (hist : List Inscription) (i : Inscription)
    (hA2 : i.regimeA2 = true) (hE : i.etat = EtatExtinction.eteinte) :
    BienFormee hist i = false := by
  simp [BienFormee, hE, hA2]

/-- **(7′) … et le quart lemme lui reste ouvert : c'est son régime ordinaire.**
    Une dette AX-2, éteinte au régime comptable et non éteinte au régime CARE, est
    bien formée au lemme 4 dès que le tiers lemme a été attesté (dépendance 4 → 3).
    La règle D-9b n'est donc pas un simple refus : elle donne à AX-2 une écriture. -/
theorem le_quart_lemme_est_le_regime_de_A2 :
    ∃ (h : Inscription) (i : Inscription),
      i.regimeA2 = true
      ∧ i.etat = EtatExtinction.eteinteEtNonEteinte
      ∧ BienFormee [h] i = true :=
  ⟨{ base with etat := EtatExtinction.indecidableAtteste, prises := [priseA]
             , critereResolution := some "constat de terrain des concernés", regimeA2 := true },
   { base with etat := EtatExtinction.eteinteEtNonEteinte, prises := [priseA, priseB]
             , regimeA2 := true },
   rfl, rfl, by decide⟩

end ProfRegPR26
