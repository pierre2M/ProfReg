/-
  SONDE · La grammaire P-C-E-D-e-d de la fiche F8 est-elle formalisable ?
  =======================================================================

  **VERSÉE LE 9 SEPTEMBRE 2026 — LOT 10.** Écrite le 8 septembre comme
  sonde de faisabilité (« on écrit la grammaire telle que le set la
  donne, on compile, et on regarde ce qui casse »), elle est versée au
  set après l'audit de découplage du 8 septembre, qui a établi qu'un
  fichier du projet n'était ni construit ni audité alors que le set
  tirait des résultats de ses théorèmes. Décompte : 273 → 286.

  ⚠️ **CE QUE CE FICHIER FORMALISE EST UN TEXTE, NON L'ARCHITECTURE.**
  Les théorèmes portent sur la GRAMMAIRE TELLE QU'ÉCRITE en §8.5, non
  sur ce qu'elle devrait être. Aucun n'établit une thèse du MRC.

  ⚠️ **ANTÉRIORITÉ — à lire avant toute citation.** La sonde a été
  écrite AVANT que les décisions 1, 2 et 3 de la tâche 12ter ne soient
  versées en §8.5.3 (8 septembre 2026). Les deux composites qu'elle
  type — `solAgricoleK1 = P⁺ + C⁺` et `chargesPersonnelK1 = e° + D⁻` —
  ont depuis été RETIRÉS de la couche T : le premier remonte en couche
  R (une chose, deux régimes de qualification, §8.4bis), le second se
  type `e` seul sous la condition de bonne formation v2 (§8.5.3bis).
  **Les énoncés restent exacts** — ces lectures étaient bien typables,
  c'est ce que la sonde a montré — **mais ils ne certifient plus un
  typage en vigueur.** `[BASE DÉCLARÉE]`

  CE QUI A ÉTÉ FAIT DES TROIS RÉSULTATS, AU 9 SEPTEMBRE
  -----------------------------------------------------
  · Résultat 3 (`respect_R1` déclaré peut mentir) — **TRAITÉ ET
    GÉNÉRALISÉ.** Le champ est supprimé de §8.5 au profit d'un contrôle
    calculé (tâche 12quater) ; PR-21 (`PR21_ChampDouble.lean`) démontre
    le fait en général pour tout contrôle calculable ; NT-ARCH §8quinquies
    en fait la cinquième forme de sur-revendication.
  · Résultat 2, moitié inter-acteurs — **TRAITÉE.** C'est PR-20
    (`PR20_MiroirInterActeurs.lean`), raccordée à `registre_augmente_coherent`
    comme la voie (b) de la note le proposait. `sans_creance_sur_soi_pas_de_lien_a_soi`
    en marque la borne.
  · Lacune du §6 (miroir des composites) — **DISSOUTE POUR LES CAS
    ATTESTÉS** par les décisions 1, 2 et 3 de 12ter, qui les ont tous
    sortis de la couche T. `miroir_non_defini_sur_les_composites` reste
    vrai du texte de §8.5, dont les champs `typage_primitive` et
    `typage_miroir` autorisent toujours « composites X+Y ».
  · **CE QUI RESTE OUVERT** — deux points, tous deux dans le texte :
    (i) §8.5.2 ne déclare toujours pas, ligne à ligne, laquelle de ses
    deux relations chaque ligne exprime : le `[CHANGEMENT DE BASE NON
    TRACÉ]` de `la_table_melange_deux_relations` **n'est pas levé** ;
    `[C-α — 28/09/2026 : LEVÉ pour les branches simples. Le « + » de la ligne
    `D−` est déclaré composite et la colonne est dédoublée (lieu de l'écriture /
    contrepartie nommée) : `PR29_TableArites.lean`. Restent quatre lacunes de
    table, `E+→D+`, `E+→C+`, `E−→C−` et `d→C−` (corrigé le 28/09 : deux
    avant correction de l'affectation), traitées cas par cas.]`
    (ii) le **signe neutre** que `e` et `d` exigent n'est nommé nulle
    part dans la grammaire, alors que ce fichier ne compile pas sans lui.

  SOURCE FORMALISÉE
  -----------------
  NT-ARCH §8.5 « Sous-couche C-MOUVEMENT-TYPE.T — typage P-C-E-D-e-d et
  règles miroir » ; §8.5.1 (définition des six primitives) ; §8.5.2
  (règles de cohérence miroir, « R1 raffinée ») ; §8.5.3 (types
  composites, arbitrage 11.3 option A). Grammaire issue de la note
  synthétique MRC × CARE × comptabilité financière (avril 2026),
  validée empiriquement par les cas K1 et K3.

  CE QUE LA SONDE ÉTABLIT — trois résultats, dont deux sont des défauts
  --------------------------------------------------------------------
  (1) Les six primitives et les composites se formalisent sans
      difficulté. Le typage est un problème résolu.
  (2) **La table des miroirs mélange DEUX relations distinctes** — une
      relation intra-écriture (débit/crédit d'une même opération) et une
      relation inter-acteurs (créancier/débiteur). C'est démontré par
      l'asymétrie partielle de la table. Le set possède déjà DEUX objets
      formels distincts pour ces deux relations (R1 d'un côté,
      le registre comptable augmenté de l'autre — [D-ED-2, 29/09/2026] ex-« l'écriture
      duale » ; la relation inter-acteurs relève en fait de l'écriture duale
      ENTRE TENEURS (N2), formalisée dans PR-35) et la grammaire n'en désigne qu'un.
  (3) **`respect_R1` est déclaré comme un booléen alors qu'il est
      calculable.** Un champ déclaré peut donc mentir : on exhibe une
      écriture qui déclare `respect_R1 = true` en violant la table.

  RÉSERVE LEVÉE — §8.5 de la v5.6 est identique à celui de la v5.5
  (contrôle du 8 septembre 2026). La sonde porte sur le texte en vigueur.

  [D-1 — 28 SEPTEMBRE 2026, décision du porteur ; audit A-4, option 1]
  La table §8.5.2 a été amendée le 18 septembre 2026 (ligne `E−` créée,
  sept lignes étendues, une ligne composite ajoutée — §8.5.2ter). La
  section 2 ci-dessous transcrit la table **du 8 septembre** et reste
  telle quelle : elle date ses théorèmes. La section 8 transcrit la
  table **du 18 septembre**, en vigueur, et y vérifie les résultats de
  la sonde — dont l'asymétrie existentielle, **`E−` compris**.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib, sans import.
-/

namespace SondePCEDed

/-! ## 1. Les six primitives et leurs signes — §8.5.1

Aucune difficulté : une énumération à six constructeurs. -/

inductive Prim where
  | P  -- Patrimoine : bien détenu et mobilisable, réifié, transmissible
  | C  -- Créance : droit attaché à un acteur identifié, non réifié
  | E  -- Engagement : promesse liant pour l'avenir, sans exigibilité
  | D  -- Dette : obligation exigible envers un créancier identifié
  | e  -- effort fourni
  | d  -- résultat répondant aux désirs
  deriving DecidableEq, Repr

/-- **Première irrégularité, mineure et signalée.** Le tableau §8.5.2
    signe `P`, `C`, `E` et `D` (`P+`, `C−`, `E+`, `D−`) mais **jamais
    `e` ni `d`**, qui apparaissent nus. Le modèle admet donc un signe
    `neutre`, que la grammaire ne nomme pas. -/
inductive Signe where
  | plus | moins | neutre
  deriving DecidableEq, Repr

structure Typage where
  prim  : Prim
  signe : Signe
  deriving DecidableEq, Repr

/-- **Les composites sont la norme, pas l'exception** (§8.5.3,
    arbitrage 11.3 option A). Un typage est donc une **liste** de
    primitives signées, non une primitive.

    Cas attestés en K1 : sol agricole `P + C`, troupeau `P + C`,
    capital patrimonial intergénérationnel `P + C`, charges de
    personnel `e + D−`. -/
abbrev Type6 := List Typage

def p (x : Prim) (s : Signe) : Typage := ⟨x, s⟩

scoped notation:max x "⁺" => p x Signe.plus
scoped notation:max x "⁻" => p x Signe.moins
scoped notation:max x "°" => p x Signe.neutre

/-! ## 2. La table des miroirs — §8.5.2, transcrite littéralement

`miroir t` donne la liste des contreparties admises pour un typage
simple `t`. Une contrepartie est elle-même un `Type6` : la liste vide
`[]` code l'absence de miroir — le cas `E+` de l'asymétrie
existentielle.

**Transcription littérale, y compris ses ambiguïtés** : la ligne `D−`
porte « C− (extinction créance) **+** e (effort de A) » là où la ligne
`P+` porte « D+ **ou** e ». Le premier est lu comme un composite, le
second comme une alternative. La table emploie donc deux connecteurs
sans les distinguer typographiquement. -/

def miroir : Typage → List Type6
  | ⟨Prim.P, Signe.plus⟩   => [[Prim.D⁺], [Prim.e°]]
  | ⟨Prim.P, Signe.moins⟩  => [[Prim.C⁺], [Prim.d°]]
  | ⟨Prim.C, Signe.plus⟩   => [[Prim.D⁺]]
  | ⟨Prim.C, Signe.moins⟩  => [[Prim.D⁻]]
  | ⟨Prim.E, Signe.plus⟩   => [[], [Prim.D⁺], [Prim.C⁺]]
  | ⟨Prim.D, Signe.plus⟩   => [[Prim.C⁺]]
  | ⟨Prim.D, Signe.moins⟩  => [[Prim.C⁻, Prim.e°]]
  | ⟨Prim.e, Signe.neutre⟩ => [[Prim.d°], [Prim.D⁻]]
  | ⟨Prim.d, Signe.neutre⟩ => [[Prim.e°], [Prim.C⁻]]
  | _                      => []      -- non tabulé

def admis (a : Typage) (b : Type6) : Prop := b ∈ miroir a

instance (a : Typage) (b : Type6) : Decidable (admis a b) := by
  unfold admis; infer_instance

/-! ## 3. Résultat 1 — l'asymétrie existentielle est bien la seule

C'est le point où la grammaire dit quelque chose de fort : `E+` est le
**seul** typage dont la table admette l'absence de contrepartie
(§8.5.2, encadré « Asymétrie autorisée — engagement existentiel »).
C'est ce que R-INTERDIT-ABSOLU instrumente. -/

/-- `E+` admet le vide comme miroir. -/
theorem E_plus_admet_le_vide : admis Prim.E⁺ [] := by decide

/-- Et il est le **seul** parmi les typages tabulés. Sans cet énoncé,
    la clause d'asymétrie existentielle serait une remarque ; elle est
    ici une propriété de la table. -/
theorem seul_E_plus_admet_le_vide :
    ¬ admis Prim.P⁺ [] ∧ ¬ admis Prim.P⁻ [] ∧ ¬ admis Prim.C⁺ []
  ∧ ¬ admis Prim.C⁻ [] ∧ ¬ admis Prim.D⁺ [] ∧ ¬ admis Prim.D⁻ []
  ∧ ¬ admis Prim.e° [] ∧ ¬ admis Prim.d° [] := by decide

/-- **L'engagement sans miroir n'est pas une dette sans créancier.**
    Le set démontre par ailleurs (`systemique_sans_creancier_viole_R1`)
    qu'une dette sans créancier viole R1. La grammaire autorise `E+`
    sans miroir. Il n'y a contradiction que si `E` et `D` sont le même
    objet — ils ne le sont pas, et la table le confirme : `D+` n'admet
    pas le vide. **La tension apparente entre R1 et l'asymétrie
    existentielle se dissout dans la distinction E / D.** -/
theorem engagement_sans_miroir_n_est_pas_dette_sans_creancier :
    Prim.E ≠ Prim.D ∧ admis Prim.E⁺ [] ∧ ¬ admis Prim.D⁺ [] := by decide

/-! ## 4. Résultat 2 — la table mélange deux relations

C'est le résultat de la sonde, et c'est un **défaut de la grammaire**,
pas de sa formalisation.

Le tableau §8.5.2 titre ses colonnes « Côté A (DÉBIT) » / « Côté B
(CRÉDIT) » — donc une relation **intra-écriture**, les deux côtés d'une
même opération dans un même livre. Mais ses lectures intuitives disent
« Toute créance d'un côté = dette de **l'autre** », « créance miroir
chez **le créancier** », « résultat reçu par **B désirant** » — donc
une relation **inter-acteurs**, entre deux livres.

Ce sont deux relations différentes, et le set possède déjà **deux
objets formels distincts** pour elles :
  · **R1** — toute écriture a une contrepartie dans le même registre ;
  · **le registre comptable augmenté** [D-ED-2, 29/09/2026] — `registre_augmente_coherent`, la contrepartie
    existe dans un registre si et seulement si elle existe dans
    l'autre.

Le test est la **symétrie**. Une relation inter-acteurs doit être
symétrique : si A détient une créance et B la dette correspondante,
alors B détient la dette et A la créance. Une relation débit/crédit
n'a aucune raison de l'être — un débit et un crédit ne jouent pas le
même rôle. -/

/-- Un couple **symétrique** de la table : `C+ ↦ D+` et `D+ ↦ C+`.
    C'est une ligne de lecture **inter-acteurs** — créancier / débiteur. -/
theorem couple_symetrique_C_D :
    admis Prim.C⁺ [Prim.D⁺] ∧ admis Prim.D⁺ [Prim.C⁺] := by decide

/-- Un couple **asymétrique** de la table : `P+ ↦ e` est admis,
    `e ↦ P+` ne l'est pas. C'est une ligne de lecture
    **intra-écriture** — « A produit par son effort », un seul acteur,
    deux côtés d'une même opération. -/
theorem couple_asymetrique_P_e :
    admis Prim.P⁺ [Prim.e°] ∧ ¬ admis Prim.e° [Prim.P⁺] := by decide

/-- **LE RÉSULTAT DE LA SONDE.** La table contient à la fois un couple
    symétrique et un couple asymétrique. Elle ne peut donc pas être
    l'expression d'une seule relation :

    · si elle était **inter-acteurs**, elle devrait être symétrique —
      `couple_asymetrique_P_e` l'interdit ;
    · si elle était **purement intra-écriture**, rien n'obligerait
      `C+ / D+` à être symétrique — et la grammaire le pose pourtant
      comme « symétrie stricte ».

    `[CHANGEMENT DE BASE NON TRACÉ]` — le mot « miroir » désigne deux
    relations dans le même tableau. La grammaire est formalisable ;
    **elle ne l'est pas en un seul type tant que ce partage n'est pas
    déclaré.** -/
theorem la_table_melange_deux_relations :
    (admis Prim.C⁺ [Prim.D⁺] ∧ admis Prim.D⁺ [Prim.C⁺])
  ∧ (admis Prim.P⁺ [Prim.e°] ∧ ¬ admis Prim.e° [Prim.P⁺]) :=
  ⟨couple_symetrique_C_D, couple_asymetrique_P_e⟩

/-- Le défaut n'est pas isolé : `P− ↦ C+` est admis, `C+ ↦ P−` ne
    l'est pas — seconde ligne asymétrique, et elle porte pourtant une
    lecture inter-acteurs (« A vend à crédit », donc l'acheteur porte
    la dette). -/
theorem second_couple_asymetrique :
    admis Prim.P⁻ [Prim.C⁺] ∧ ¬ admis Prim.C⁺ [Prim.P⁻] := by decide

/-! ## 5. Résultat 3 — un booléen déclaré peut mentir

§8.5 pose `respect_R1 : Booléen — vérification que (typage_primitive,
typage_miroir) appartient à la table des compatibilités miroir`.

C'est un **champ déclaré** dont le contenu est **calculable**. Rien
n'oblige alors le champ à dire la vérité de la table. -/

structure EcritureTypee where
  typage      : Typage
  typageMiroir : Type6
  /-- Le champ tel que §8.5 le pose. -/
  respectR1Declare : Bool

/-- Ce que la table dit réellement du couple. -/
def respectR1Calcule (x : EcritureTypee) : Prop :=
  admis x.typage x.typageMiroir

instance (x : EcritureTypee) : Decidable (respectR1Calcule x) := by
  unfold respectR1Calcule; infer_instance

/-- **Le champ déclaré peut contredire la table.** On exhibe une
    écriture qui déclare respecter R1 avec un couple que la table
    n'admet pas — `d° ↦ P+`, absent de la ligne `d`.

    Conséquence : `respect_R1` ne doit pas être un champ mais un
    **prédicat calculé**, exactement comme `opposabilite_exhibe_statut`
    (PR-14) exhibe le statut au lieu de le déclarer. C'est la règle de
    rédaction de NT-ARCH §8bis appliquée à un schéma de fiche plutôt
    qu'à un énoncé de théorème. -/
theorem respect_R1_declare_peut_mentir :
    ∃ x : EcritureTypee, x.respectR1Declare = true ∧ ¬ respectR1Calcule x := by
  refine ⟨{ typage := Prim.d°
          , typageMiroir := [Prim.P⁺]
          , respectR1Declare := true }, rfl, ?_⟩
  decide

/-- Et la réciproque : une écriture parfaitement conforme à la table
    peut déclarer ne pas la respecter. Le champ est **indépendant** de
    ce qu'il prétend enregistrer, dans les deux sens. -/
theorem respect_R1_declare_peut_se_sous_estimer :
    ∃ x : EcritureTypee, x.respectR1Declare = false ∧ respectR1Calcule x := by
  refine ⟨{ typage := Prim.C⁺
          , typageMiroir := [Prim.D⁺]
          , respectR1Declare := false }, rfl, ?_⟩
  decide

/-! ## 6. Les composites — aucune difficulté, et une lacune -/

/-- Le sol agricole de K1 : propriété privée (P) **et** créance
    écologique CARE (C). Le composite se type sans effort. -/
def solAgricoleK1 : Type6 := [Prim.P⁺, Prim.C⁺]

/-- Les charges de personnel de K1 : effort des salariés reçu (e)
    **et** remboursement partiel de la dette humaine cumulée (D−). -/
def chargesPersonnelK1 : Type6 := [Prim.e°, Prim.D⁻]

theorem composites_bien_types :
    solAgricoleK1.length = 2 ∧ chargesPersonnelK1.length = 2 := by decide

/-- **Lacune : la table des miroirs ne porte que sur les types
    simples.** `miroir` est défini sur `Typage`, pas sur `Type6`.
    Or les composites sont « la norme » (§8.5.3). La grammaire ne dit
    donc pas quel miroir admet `P + C`, qui est le cas le plus attesté
    de tout le corpus K1.

    Deux extensions possibles, non tranchées : le miroir d'un composite
    est-il le composite des miroirs (distributivité), ou un miroir
    propre à déclarer ? La première est calculable, la seconde suppose
    une table nouvelle. **La grammaire ne le dit pas.** -/
theorem miroir_non_defini_sur_les_composites :
    ∃ t : Type6, t.length = 2 ∧ (∀ a : Typage, [a] ≠ t) := by
  refine ⟨solAgricoleK1, rfl, ?_⟩
  intro a h
  have : (1 : Nat) = 2 := congrArg List.length h
  exact absurd this (by decide)

/-! ## 7. Gardes -/

/-- **La sonde ne juge pas la grammaire.** Les six primitives se
    formalisent, les composites aussi, et l'asymétrie existentielle est
    une propriété démontrable de la table. Ce qui est mis en défaut est
    le **mot « miroir »**, employé pour deux relations, et le **champ
    `respect_R1`**, déclaré là où il est calculable. -/
theorem la_sonde_ne_condamne_pas_le_typage :
    admis Prim.C⁺ [Prim.D⁺] ∧ admis Prim.E⁺ [] ∧ solAgricoleK1.length = 2 := by
  decide

/-- **La sonde ne propose rien.** Elle ne dit pas laquelle des deux
    relations la grammaire devrait retenir, ni si `respect_R1` doit
    devenir un prédicat ou disparaître. Ces décisions sont des actes
    de porteur, et ce fichier n'en prend aucun. -/
theorem la_sonde_ne_tranche_pas :
    (admis Prim.P⁺ [Prim.e°] ∧ ¬ admis Prim.e° [Prim.P⁺])
  ∧ (admis Prim.C⁺ [Prim.D⁺] ∧ admis Prim.D⁺ [Prim.C⁺]) :=
  ⟨couple_asymetrique_P_e, couple_symetrique_C_D⟩

/-! ## 8. La table du 18 septembre 2026 — en vigueur (D-1, 28/09/2026)

Transcription de NT-ARCH §8.5.2 après les décisions 2 à 7 du 18 septembre
(§8.5.2ter). Mêmes conventions que la section 2 : `[]` code l'absence de
miroir ; le « + » de la ligne `D−` est un composite, les « ou » sont des
alternatives.

**Ce qui n'est pas transcrit.** La ligne composite `P+ + D+ ↔ P− + D−`
(transfert de chose entre deux acteurs) a pour clé un composite ; or
`miroir1809`, comme `miroir`, est défini sur les typages simples. Elle
reste hors de cette fonction : c'est la lacune de
`miroir_non_defini_sur_les_composites`, désormais **habitée** par une
ligne de la table en vigueur. Les conditions d'arité (colonne « nature de
la relation ») et la condition `destinataire_effort = SANS_BENEFICIAIRE`
de la branche `P− ↦ e` ne sont pas formalisées. -/

def miroir1809 : Typage → List Type6
  | ⟨Prim.P, Signe.plus⟩   => [[Prim.D⁺], [Prim.e°], [Prim.P⁻]]
  | ⟨Prim.P, Signe.moins⟩  => [[Prim.C⁺], [Prim.d°], [Prim.P⁺], [Prim.e°]]
  | ⟨Prim.C, Signe.plus⟩   => [[Prim.D⁺]]
  | ⟨Prim.C, Signe.moins⟩  => [[Prim.D⁻]]
  | ⟨Prim.E, Signe.plus⟩   => [[], [Prim.D⁺], [Prim.C⁺], [Prim.e°], [Prim.E⁻], [Prim.D⁻]]
  | ⟨Prim.E, Signe.moins⟩  => [[Prim.C⁻], [Prim.D⁺], [Prim.d°]]
  | ⟨Prim.D, Signe.plus⟩   => [[Prim.C⁺], [Prim.D⁻]]
  | ⟨Prim.D, Signe.moins⟩  => [[Prim.C⁻, Prim.e°], [Prim.D⁺]]
  | ⟨Prim.e, Signe.neutre⟩ => [[Prim.d°], [Prim.D⁻], [Prim.E⁺], [Prim.P⁻]]
  | ⟨Prim.d, Signe.neutre⟩ => [[Prim.e°], [Prim.C⁻]]
  | _                      => []      -- non tabulé

def admis1809 (a : Typage) (b : Type6) : Prop := b ∈ miroir1809 a

instance (a : Typage) (b : Type6) : Decidable (admis1809 a b) := by
  unfold admis1809; infer_instance

/-- **L'asymétrie existentielle, sur la table en vigueur.** `E+` admet le
    vide, et **aucun autre typage tabulé** ne l'admet — `E−` compris, que
    la table du 18/09 crée et dont elle précise qu'il « n'hérite PAS de
    l'exception à ∅ ». C'est l'énoncé que NT-ARCH §8.5.2 et §8.5.6
    citent pour la table en vigueur ; `seul_E_plus_admet_le_vide` le
    porte pour la table du 8/09. -/
theorem seul_E_plus_admet_le_vide_table_1809 :
    admis1809 Prim.E⁺ []
  ∧ ¬ admis1809 Prim.P⁺ [] ∧ ¬ admis1809 Prim.P⁻ [] ∧ ¬ admis1809 Prim.C⁺ []
  ∧ ¬ admis1809 Prim.C⁻ [] ∧ ¬ admis1809 Prim.E⁻ [] ∧ ¬ admis1809 Prim.D⁺ []
  ∧ ¬ admis1809 Prim.D⁻ [] ∧ ¬ admis1809 Prim.e° [] ∧ ¬ admis1809 Prim.d° [] := by
  decide

/-- **Les résultats de la sonde tiennent sur la table en vigueur.** Le
    couple `C+ / D+` reste symétrique ; `P+ ↦ e` reste admis sans
    réciproque (la ligne `e` gagne `E+` et `P−`, pas `P+`) ; `P− ↦ C+`
    reste sans réciproque. La table du 18/09 mêle donc toujours deux
    relations — mais elle **le déclare** désormais, ligne à ligne, dans sa
    colonne « nature de la relation » : ce qui était un changement de base
    non tracé est devenu une base déclarée. Le théorème établit le fait ;
    il ne dit rien de la justesse des arités déclarées. -/
theorem les_resultats_de_la_sonde_tiennent_table_1809 :
    (admis1809 Prim.C⁺ [Prim.D⁺] ∧ admis1809 Prim.D⁺ [Prim.C⁺])
  ∧ (admis1809 Prim.P⁺ [Prim.e°] ∧ ¬ admis1809 Prim.e° [Prim.P⁺])
  ∧ (admis1809 Prim.P⁻ [Prim.C⁺] ∧ ¬ admis1809 Prim.C⁺ [Prim.P⁻]) := by
  decide

end SondePCEDed
