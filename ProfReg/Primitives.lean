/-
  Primitives.lean — les types partagés du set, en un seul endroit
  ===============================================================

  Créé le 7 septembre 2026 (tâche 3quinquies du plan d'Étape 3),
  décision du porteur.

  POURQUOI CE FICHIER EXISTE
  --------------------------
  Les fichiers de vérification préexistants (V3, V4, V10) importent
  Mathlib transitivement — V10 → V3 → V1 → `Mathlib.Data.Real.Basic`.
  Les fichiers du programme de preuve écrits en septembre 2026 (PR-3,
  PR-8, PR-10, PR-15, PR-16) n'en ont pas besoin, et ne pouvaient donc
  pas importer les premiers sans se charger de Mathlib. Ils ont
  RECOPIÉ les types.

  Les copies ont dérivé. Constat du 7 septembre 2026 :
    · `StatutDette` : 3 constructeurs en V4, 4 en PR-3 — dont
      `critique`, qui **fusionnait deux types du set en un seul**
      (voir plus bas) ;
    · `ContexteProspectif` : 5 champs en V10, 4 en PR-8 ;
    · `StatutSeuil`, `LegitimiteRepresentant`, `HorizonTemporel` :
      identiques, mais rien ne garantissait qu'ils le restent.

  Ce fichier supprime la cause plutôt que de corriger l'effet.
  Les types n'ont jamais eu besoin de Mathlib ; seules les PREUVES des
  fichiers V en ont besoin. On sépare donc les deux :
    · `Primitives.lean` — sans Mathlib, importé par tout le monde ;
    · `V3/V4/V10Verification.lean` — gardent Mathlib pour leurs
      preuves, et importent leurs types d'ici.

  Effet secondaire recherché : les fichiers PR redeviennent
  vérifiables dans un environnement sans cache Mathlib.

  CONVENTION DE NOMMAGE
  ---------------------
  Chaque type reste dans le namespace où il vivait, pour qu'aucune
  référence existante ne casse. C'est pourquoi ce fichier ouvre deux
  namespaces plutôt qu'un.

  Porteur : Pierre Musseau. Lean 4 pur, sans Mathlib, sans import.
-/

namespace ProfReg

/-! ## Couche 0 — régime d'obligation

NT-ARCH §2. Anciennement déclaré dans `V3Verification.lean`. -/

inductive RegimeObligation where
  | actoriel   : RegimeObligation
  | systemique : RegimeObligation
  | hybride    : RegimeObligation
  deriving DecidableEq, Repr

/-! ## Couche 1 — C-STATUT-DETTE et la machine d'états

NT-ARCH §3 et §4. Anciennement déclarés dans `V4Verification.lean`.

⚠️ **`StatutDette` et `NiveauRIA` sont DEUX TYPES, et c'est voulu.**

`NiveauRIA` signifie *niveau de déclenchement de R-INTERDIT-ABSOLU*.
CRITIQUE est un **niveau de la règle**, non un **état de la dette**.
NT-G2 §3.1, note de déclenchement, l'écrit trois fois :
  « R-INTERDIT-ABSOLU déclenche niveau DELIBERATION (non CRITIQUE) » ;
  « le niveau CRITIQUE ne s'applique qu'une fois des porteurs
    identifiés » ;
  « ATTRIBUEE → CRITIQUE est la seule voie de libération du niveau
    CRITIQUE ».

Source de la règle : Jonas, *Le Principe Responsabilité*, 1979 /
trad. Cerf 1990 — R-INTERDIT-ABSOLU est l'opérateur formel de
l'heuristique de la peur. Source du déclenchement du niveau CRITIQUE :
Morizot & Neyret 2026, amendement A3.

`PR3_AttributionSeuil.lean` avait fusionné les deux types en un seul
`StatutDette` à quatre constructeurs. Corrigé le 7 septembre 2026. -/

inductive StatutDette where
  | attribuee      : StatutDette   -- porteur DID identifié
  | nonAttribuee   : StatutDette   -- dette systémique sans porteur
  | enDeliberation : StatutDette   -- phase INVENTAIRE ou DELIBERATION active
  deriving DecidableEq, Repr

inductive NiveauRIA where
  | deliberation : NiveauRIA   -- avant porteur : oblige à délibérer
  | critique     : NiveauRIA   -- après porteur identifié : blocage complet
  deriving DecidableEq, Repr

/-- Inventaire des acteurs mobilisés (phase B2).
    Sous-type : la non-vacuité est garantie par construction. -/
def InventaireNonVide := { l : List String // l ≠ [] }

/-- NT-ARCH §4 — machine d'états. `NONATTRIBUEE → CRITIQUE` est
    interdite ; la seule transition autorisée depuis NONATTRIBUEE est
    vers DELIBERATION. -/
def transition_valide : StatutDette → NiveauRIA → Prop
  | StatutDette.nonAttribuee,   NiveauRIA.critique     => False  -- interdit
  | StatutDette.nonAttribuee,   NiveauRIA.deliberation => True   -- autorisé
  | StatutDette.enDeliberation, NiveauRIA.deliberation => True   -- autorisé
  | StatutDette.enDeliberation, NiveauRIA.critique     => False  -- pas encore
  | StatutDette.attribuee,      NiveauRIA.critique     => True   -- autorisé
  | StatutDette.attribuee,      NiveauRIA.deliberation => True   -- autorisé

/-! ## Couche 0 — seuil d'entrée dans la communauté morale

NT-ARCH §5.1 : `seuilentreecommunautemorale ∈ { SENTIENCE /
FINALITEIMMANENTE / NONDECLARE }`.

Ancrage : NT-G7 §2 (Nussbaum 2006, SENTIENCE) et NT-G2 §3
(Jonas 1979, FINALITEIMMANENTE).

Typé **`seuil-valuatif`** par l'Annexe méthodologique §A.14.7 : PR-10
s'y applique, et l'attribution d'une obligation exige donc le
quadruplet complet « statut du seuil ». -/

inductive SeuilCommunauteMorale where
  | sentience
  | finaliteImmanente
  | nonDeclare
  deriving DecidableEq, Repr

end ProfReg

namespace V10

open ProfReg

/-! ## Contexte planétaire — AM-G7-08 / AM-ARCH-01

Anciennement déclarés dans `V10Verification.lean`. -/

inductive PorteeAsymetrie where
  | locale
  | systematique
  | spatialePlanetaire
  deriving DecidableEq, Repr

abbrev PorteurDID := Option String

structure ContextePlanetaire where
  porteeAsy   : PorteeAsymetrie
  regimeObl   : RegimeObligation
  statutDette : StatutDette
  porteurDID  : PorteurDID
  deriving Repr

def estPlanetaireSansPorteur (c : ContextePlanetaire) : Prop :=
  c.porteeAsy  = PorteeAsymetrie.spatialePlanetaire ∧
  c.regimeObl  = RegimeObligation.systemique ∧
  c.porteurDID = none

/-- Règle d'architecture (Couche 1), ajoutée le 7 septembre 2026 :
    un contexte planétaire sans porteur a pour statut `nonAttribuee`.
    Elle se déclare, elle ne se démontre pas — même statut que
    `RegleAM_ARCH_01`. Sans elle, l'hypothèse planétaire des théorèmes
    V10a serait inerte. -/
def ReglePlanetaire (c : ContextePlanetaire) : Prop :=
  estPlanetaireSansPorteur c → c.statutDette = StatutDette.nonAttribuee

/-! ## Représentation prospective — NT-ARCH §5.2 (B3) -/

inductive HorizonTemporel where
  | institutionnel
  | intergenerationnel
  | profond
  | planetaire        -- AM-G7-08 : horizon sans porteur institutionnel désignable
  -- [D-2 CLOSE LE 27/09/2026 — décision de porteur] valeur `eea` SUPPRIMÉE.
  -- Un horizon géologique équivaut à l'horizon planétaire et ne peut le dépasser ;
  -- l'EEA (Boyer & Petersen 2018, §4.1) est un agrégat de conditions de sélection
  -- passées, non un horizon de responsabilité. Aucun théorème ne nommait la valeur.
  deriving DecidableEq, Repr

inductive LegitimiteRepresentant where
  | pratique       -- **défaut** — conditionRefutation OBLIGATOIRE
  | deliberative
  | juridique
  | planetaireNonDesignee  -- AM-G7-08 révisé : aucune institution désignable
  deriving DecidableEq, Repr

/-- NT-ARCH §5.2. Le champ `statutDette` était absent de la copie de
    `PR8_RefutationPratique.lean` ; il est ici, unique. -/
structure ContexteProspectif where
  statutDette    : StatutDette
  horizon        : HorizonTemporel
  porteurDID     : PorteurDID
  legitimite     : LegitimiteRepresentant
  /-- Texte. `none` = non renseignée. OBLIGATOIRE si `legitimite` vaut
      `pratique` ou `planetaireNonDesignee`. -/
  condRefutation : Option String
  deriving Repr

def exigeRepresentationProspective (c : ContexteProspectif) : Prop :=
  c.horizon    = HorizonTemporel.planetaire ∧
  c.porteurDID = none

def condRefutationRenseignee (c : ContexteProspectif) : Prop :=
  c.condRefutation ≠ none

end V10
