/-
  PR-20 · `lien_inter_acteurs_porte_par_un_registre_augmente`
  =====================================================

  [D-ED-2, 29/09/2026] RENOMMÉ, ex-`miroir_inter_acteurs_est_une_ecriture_duale`.
  Ce fichier montre que le lien inter-acteurs, pris sur une relation
  GLOBALE `Actor → Actor → Bool`, se porte dans un registre comptable
  augmenté (N3). Il ne formalise PAS l'écriture duale au sens du porteur
  (N2 : deux registres tenus par deux entités distinctes) : aucun registre
  n'y a de teneur, et la symétrie de `lien` est obtenue par définition
  (`c a b || c b a`), non par deux inscriptions indépendantes
  `[RAISONNEMENT AUTORÉFÉRENTIEL pour N2]`. N2 est formalisée dans
  `PR35_EcritureDuale.lean`, qui réutilise `TypageIA` et `miroirIA`.

  Formalisation de la **moitié inter-acteurs** de la grammaire
  P-C-E-D-e-d (NT-ARCH §8.5.2), décidée le 8 septembre 2026 après la
  sonde `Sonde_PCEDed.lean`.

  CE QU'IL ÉTABLIT
  ----------------
  Les lignes inter-acteurs de la table des miroirs sont des **instances
  du registre comptable augmenté** — `RegistreComptableAugmente` / `registre_augmente_coherent`,
  compilé le 7 septembre. Ce n'est pas une analogie : le socle de L2
  est une relation `Actor → Actor → Bool` dont R1 exige la **symétrie**
  (`R1_actoriel`), et le lien créancier / débiteur est symétrique par
  construction. **L2 reçoit ici son premier contenu comptable.**

  LE POINT QUI DÉNOUE LA SONDE
  ----------------------------
  La sonde établissait que le mot « miroir » désigne deux relations. La
  difficulté résiduelle était celle-ci : si A détient une créance sur B,
  B ne détient pas une créance sur A — il détient une dette. La relation
  ne semblait donc pas symétrique, et L2 ne semblait pas s'appliquer.

  La sortie est de distinguer **le lien** et **le typage** :
    · le LIEN entre A et B est symétrique — il existe des deux côtés ;
    · le TYPAGE est opposé — C d'un côté, D de l'autre.
  R1 porte sur le lien, la table porte sur le typage. **Les lignes dites
  asymétriques de §8.5.2 le sont parce qu'elles TYPENT, non parce
  qu'elles LIENT.**

  CE QU'IL RÉVÈLE, ET QUI N'ÉTAIT PAS PRÉVU
  -----------------------------------------
  Sous transcription littérale, **un seul couple de la table satisfait
  le test de symétrie** : `C+ / D+`. Les lignes `C−` et `E+` portent des
  gloses inter-acteurs sans que leur converse figure au tableau. La
  moitié inter-acteurs doit donc être **complétée**, pas seulement
  extraite — et §6 le fait comme une PROPOSITION déclarée, non comme
  une lecture de la source.

  RÉSERVE LEVÉE
  -------------
  §8.5 était formalisé d'après `MRC_v5.5_NT-ARCH`, la v5.6 ne reprenant
  pas la sous-couche T dans le corps que j'avais consulté. **Contrôle
  fait le 8 septembre 2026 : §8.5, §8.5.1, §8.5.2 et §8.5.3 de la v5.6
  sont identiques à ceux de la v5.5** — mêmes six champs, mêmes neuf
  lignes de la table, mêmes cinq cas composites. Le fichier porte donc
  sur le texte en vigueur.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.LotL2_PR2_PR14`.
-/

import ProfReg.LotL2_PR2_PR14

namespace ProfRegPR20

open ProfRegLot

/-! ## 1. Le lien inter-acteurs est symétrique — le typage ne l'est pas

`creance a b = true` se lit : **A détient une créance sur B**. La
relation est orientée : elle distingue le créancier du débiteur.

Le **lien** d'obligation, lui, ne l'est pas : il existe entre A et B dès
que l'un des deux détient une créance sur l'autre. C'est ce lien que R1
exige symétrique, et il l'est par construction. -/

/-- Relation orientée : `creance a b` = A détient une créance sur B. -/
abbrev Creance := Actor → Actor → Bool

/-- Le lien d'obligation entre deux acteurs — **non orienté**. -/
def lien (c : Creance) : Actor → Actor → Bool :=
  fun a b => c a b || c b a

/-- **Le lien satisfait R1.** C'est la condition exacte que
    `R1_preserved_under_base_change` demande de son socle, et elle est
    ici vraie **par construction**, sans hypothèse sur `c`. -/
theorem lien_est_symetrique (c : Creance) : R1_actoriel (lien c) := by
  intro a b h
  unfold lien at h ⊢
  cases hab : c a b <;> cases hba : c b a <;>
    simp [hab, hba] at h ⊢

/-- Et l'orientation, elle, **n'est pas** symétrique : il existe une
    créance de A sur B sans créance de B sur A. Sans cet énoncé, le
    précédent se lirait comme si créancier et débiteur étaient
    interchangeables. -/
theorem la_creance_n_est_pas_symetrique :
    ∃ c : Creance, ∃ a b : Actor, c a b = true ∧ c b a = false := by
  refine ⟨fun x y => x == "A" && y == "B", "A", "B", ?_, ?_⟩ <;> decide

/-! ## 2. La moitié inter-acteurs se porte dans un registre comptable augmenté

On construit l'instance : le socle de L2 est le lien, le registre
financier porte un montant, le registre de communalité porte une
mention. **Rien n'est ajouté à L2** — on lui fournit son premier
contenu comptable. -/

/-- Registre financier : 1 si le lien existe, 0 sinon. -/
def registreFinancier (c : Creance) : Actor → Actor → Nat :=
  fun a b => if lien c a b then 1 else 0

/-- Ce que le registre de communalité porte. **Une énumération, pas
    une chaîne libre** — et ce n'est pas un détail de style : la
    première version de ce fichier employait `String`, et l'audit
    d'axiomes a montré que la comparaison de littéraux de chaîne tire
    `Classical.choice`. Le contrôle posé le matin même — « neuf
    théorèmes, et ce sont exactement ceux qui passent par les réels » —
    a donc sonné sur quatre théorèmes de ce fichier.

    Le remède est aussi une meilleure modélisation : une mention dont
    les valeurs sont énumérables se type par une énumération. Même
    leçon que `usageAgregat` (option D, le même jour). -/
inductive MentionCom where
  | inscrit  -- le lien d'obligation est inscrit
  | absent   -- aucun lien
  deriving DecidableEq, Repr

/-- Registre de communalité : la mention inscrite, ou son absence. -/
def registreCommunalite (c : Creance) : Actor → Actor → MentionCom :=
  fun a b => if lien c a b then MentionCom.inscrit else MentionCom.absent

theorem compat_financier (c : Creance) :
    CompatibleExtension 1 (lien c) (registreFinancier c) := by
  intro a b
  unfold registreFinancier
  cases lien c a b <;> simp

theorem compat_communalite (c : Creance) :
    CompatibleExtension MentionCom.inscrit (lien c)
      (registreCommunalite c) := by
  intro a b
  unfold registreCommunalite
  cases lien c a b <;> simp

/-- **L'instance.** Toute relation de créance engendre un registre
    comptable augmenté au sens de L2. -/
def registreAugmenteDe (c : Creance) : RegistreComptableAugmente Nat MentionCom :=
  { socle     := lien c
  , pFin      := registreFinancier c
  , pCom      := registreCommunalite c
  , pleinFin  := 1
  , pleinCom  := MentionCom.inscrit
  , compatFin := compat_financier c
  , compatCom := compat_communalite c }

/-- **PR-20.** La contrepartie d'un lien inter-acteurs existe dans le
    registre financier **si et seulement si** elle existe dans le
    registre de communalité.

    C'est `registre_augmente_coherent` appliqué à la grammaire
    P-C-E-D-e-d. La coordination des deux comptabilités sur l'existence
    du lien n'est plus posée : elle est **héritée d'un théorème
    compilé**. -/
theorem lien_inter_acteurs_porte_par_un_registre_augmente (c : Creance) :
    ∀ a b, registreFinancier c a b = 1
         ↔ registreCommunalite c a b = MentionCom.inscrit :=
  registre_augmente_coherent (registreAugmenteDe c)

/-- Et R1 survit dans les deux registres — `registre_augmente_preserve_R1`
    appliqué à la même instance. L'hypothèse de symétrie du socle est
    fournie par `lien_est_symetrique`, donc **jamais supposée**. -/
theorem R1_tient_dans_les_deux_registres (c : Creance) :
    (∀ a b, registreFinancier c a b = 1 → registreFinancier c b a = 1)
  ∧ (∀ a b, registreCommunalite c a b = MentionCom.inscrit
            → registreCommunalite c b a = MentionCom.inscrit) :=
  registre_augmente_preserve_R1 (registreAugmenteDe c) (lien_est_symetrique c)

/-! ## 3. Le typage est opposé — c'est là que la table dit quelque chose -/

inductive Role where
  | creancier | debiteur
  deriving DecidableEq, Repr

inductive TypageIA where
  | Cplus | Dplus | Cmoins | Dmoins
  deriving DecidableEq, Repr

/-- Le typage attaché à chaque rôle, pour une **naissance** de lien
    (ligne `C+ / D+` de §8.5.2, annotée « symétrie stricte »). -/
def typageNaissance : Role → TypageIA
  | Role.creancier => TypageIA.Cplus
  | Role.debiteur  => TypageIA.Dplus

/-- Et pour une **extinction** (ligne `C− / D−`). -/
def typageExtinction : Role → TypageIA
  | Role.creancier => TypageIA.Cmoins
  | Role.debiteur  => TypageIA.Dmoins

/-- **Les deux rôles ne portent jamais le même typage.** Le lien est
    symétrique, les rôles sont opposés — c'est la formulation exacte
    de « toute créance d'un côté = dette de l'autre ». -/
theorem roles_opposes :
    typageNaissance Role.creancier ≠ typageNaissance Role.debiteur
  ∧ typageExtinction Role.creancier ≠ typageExtinction Role.debiteur := by
  decide

/-- Et le typage **détermine le rôle** : on peut lire le rôle sur
    l'écriture, sans information extérieure. C'est ce qui rend la
    moitié inter-acteurs contrôlable par un tiers. -/
def roleDeTypage : TypageIA → Role
  | TypageIA.Cplus  => Role.creancier
  | TypageIA.Cmoins => Role.creancier
  | TypageIA.Dplus  => Role.debiteur
  | TypageIA.Dmoins => Role.debiteur

theorem le_typage_determine_le_role (r : Role) :
    roleDeTypage (typageNaissance r) = r
  ∧ roleDeTypage (typageExtinction r) = r := by
  cases r <;> exact ⟨rfl, rfl⟩

/-! ## 4. La garde essentielle — même existence, pas même valeur

`registre_augmente_non_equivalence` (L2) exhibe deux registres duaux
cohérents qui divergent hors du point plein. Transposé ici :

> Les deux registres ne peuvent pas se contredire **sur l'existence de
> la contrepartie** ; hors du point plein, leurs valeurs sont libres.

Sans cette garde, PR-20 se lirait comme une exigence d'harmonisation
des évaluations — ce que le set refuse depuis la voie 3 de §A.6.

PORTÉE EXACTE DU TÉMOIN — correction du 8 septembre 2026
--------------------------------------------------------
Le commentaire d'origine disait « on n'exige pas que les deux
comptabilités disent la même chose », ce qui **annonçait plus que
l'énoncé**. Le témoin du théorème est `c := fun _ _ => false`, donc un
**socle vide** : les deux registres divergent là où il n'y a **aucun
lien** (0 contre 7). Sur un lien existant, `registreFinancier` et
`registreFinancierBis` valent **tous deux 1**, par construction — cette
instance n'a pas de quoi exprimer un montant, conformément à CONV-10
(le point plein reconnaît le lien, il ne le valorise pas).

L'énoncé est exact ; c'était sa **documentation** qui promettait une
liberté d'évaluation que le témoin ne montre pas. **Sixième forme
candidate de sur-revendication** (NT-ARCH §8septies) : *énoncé exact,
témoin dégénéré au regard de ce que la documentation annonce.* Comme
les formes 3, 4 et 5, elle n'a **aucun crible** — et comme elles, elle a
été trouvée **par hasard**, en vérifiant autre chose. Quatre fois sur
quatre. -/

/-- Un **second** registre financier, tout aussi compatible : il porte
    la même valeur pleine et diverge partout ailleurs. -/
def registreFinancierBis (c : Creance) : Actor → Actor → Nat :=
  fun a b => if lien c a b then 1 else 7

theorem compat_financier_bis (c : Creance) :
    CompatibleExtension 1 (lien c) (registreFinancierBis c) := by
  intro a b
  unfold registreFinancierBis
  cases lien c a b <;> simp

def registreAugmenteBis (c : Creance) : RegistreComptableAugmente Nat MentionCom :=
  { registreAugmenteDe c with
    pFin := registreFinancierBis c
  , compatFin := compat_financier_bis c }

/-- **Accord sur l'existence, pas sur la valeur.** Deux registres
    augmentés sur le même socle, toutes deux cohérentes au sens de L2,
    peuvent donner des valeurs différentes hors du point plein.

    C'est `registre_augmente_non_equivalence` transposé à la grammaire :
    les deux registres ne peuvent pas se contredire **sur l'existence
    de la contrepartie**, et hors du point plein leurs valeurs sont
    libres. Sans cet énoncé, PR-20 se lirait comme une exigence
    d'harmonisation des évaluations — ce que le set refuse depuis la
    voie 3 de l'Annexe §A.6.

    **Portée du témoin (8 septembre 2026)** : la divergence est exhibée
    sur un **socle vide**. Ce théorème n'établit donc pas que deux
    évaluations d'une dette *existante* peuvent différer — cette
    instance ne sait pas exprimer de montant. Voir §4. -/
theorem accord_sur_l_existence_pas_sur_la_valeur :
    ∃ (c : Creance) (a b : Actor),
      (∀ x y, (registreAugmenteDe c).pFin x y = 1
              ↔ (registreAugmenteDe c).pCom x y = MentionCom.inscrit)
    ∧ (∀ x y, (registreAugmenteBis c).pFin x y = 1
              ↔ (registreAugmenteBis c).pCom x y = MentionCom.inscrit)
    ∧ (registreAugmenteDe c).pFin a b ≠ (registreAugmenteBis c).pFin a b := by
  refine ⟨fun _ _ => false, "A", "B",
          registre_augmente_coherent (registreAugmenteDe _),
          registre_augmente_coherent (registreAugmenteBis _), ?_⟩
  simp [registreAugmenteDe, registreAugmenteBis, registreFinancier,
        registreFinancierBis, lien]

/-! ## 5. L'engagement existentiel n'appartient pas à cette moitié

`E+` sans miroir est le cas de R-INTERDIT-ABSOLU : un engagement pris
envers un acteur **non tracé**. Un lien inter-acteurs suppose deux
acteurs identifiés ; l'asymétrie existentielle sort donc de cette
moitié par construction, et non par oubli.

C'est la contrepartie du résultat de la sonde
(`engagement_sans_miroir_n_est_pas_dette_sans_creancier`) : la
distinction E / D partage aussi les deux moitiés de la table. -/

/-- Sans créance dans aucun sens, aucun lien — donc aucun registre
    augmenté à former. L'engagement existentiel relève de l'autre moitié. -/
theorem sans_creance_aucun_lien (c : Creance) (a b : Actor)
    (hab : c a b = false) (hba : c b a = false) :
    lien c a b = false := by
  unfold lien; simp [hab, hba]

/-- Et le registre de communalité l'enregistre comme absence, non comme
    lien de valeur nulle. **Un engagement sans contrepartie n'est pas
    une dette de zéro.** -/
theorem absence_n_est_pas_lien_nul (c : Creance) (a b : Actor)
    (hab : c a b = false) (hba : c b a = false) :
    registreCommunalite c a b = MentionCom.absent := by
  unfold registreCommunalite
  simp [sans_creance_aucun_lien c a b hab hba]

/-! ## 6. Le diagnostic — la table doit être complétée, pas extraite

*Cette section est une **proposition déclarée**, non une lecture de la
source.*

Sous transcription littérale (`Sonde_PCEDed.lean`), **un seul couple de
§8.5.2 satisfait le test de symétrie** : `C+ ↦ D+` et `D+ ↦ C+`. Les
lignes `C−` et `E+` portent pourtant des gloses inter-acteurs sans que
leur converse figure au tableau — `D− ↦ C−+e` est un composite, et
`C+ ↦ E+` n'existe pas.

La moitié inter-acteurs proposée ici est donc **symétrique par
construction** (§1) plutôt que constatée sur la table. C'est un choix,
et il complète la source au lieu de la transcrire. -/

/-- La table inter-acteurs telle qu'elle devrait être : deux lignes,
    et la converse de chacune. -/
def miroirIA : TypageIA → TypageIA
  | TypageIA.Cplus  => TypageIA.Dplus
  | TypageIA.Dplus  => TypageIA.Cplus
  | TypageIA.Cmoins => TypageIA.Dmoins
  | TypageIA.Dmoins => TypageIA.Cmoins

/-- **Elle est involutive** — donc symétrique, pour les quatre typages
    et non pour un seul. C'est la propriété que la table littérale
    n'avait pas, et c'est ce que la complétion apporte. -/
theorem miroirIA_involutive (t : TypageIA) : miroirIA (miroirIA t) = t := by
  cases t <;> rfl

/-- Et elle ne fixe aucun typage : le miroir change toujours de rôle.
    Une écriture ne peut pas être son propre miroir inter-acteurs. -/
theorem miroirIA_sans_point_fixe (t : TypageIA) : miroirIA t ≠ t := by
  cases t <;> decide

/-! ## 7. Gardes -/

/-- **PR-20 ne dit pas qui est le créancier.** Deux relations de
    créance opposées engendrent le même lien, donc le même registre
    augmenté. L'orientation est une donnée d'inscription, non un résultat
    du théorème. -/
theorem PR20_ne_designe_pas_le_creancier :
    ∃ c₁ c₂ : Creance, ∃ a b : Actor,
      c₁ a b = true ∧ c₂ b a = true ∧ lien c₁ a b = lien c₂ a b := by
  refine ⟨fun x y => x == "A" && y == "B", fun x y => x == "B" && y == "A",
          "A", "B", by decide, by decide, by decide⟩

/-- **Sans créance de `a` sur lui-même, pas de lien de `a` à `a`.**
    *Portée visée — déclarée, non établie par l'énoncé :* PR-20 ne couvre pas les lignes intra-écriture. `P+ ↦ e` — « A
    produit par son effort » — met en jeu un seul acteur ; aucun lien
    inter-acteurs ne s'y forme. La moitié restante relève de R1 dans un
    même registre, et **ce fichier n'en traite pas**. -/
-- [B-10, 28/09/2026 — RENOMMÉ, ex-`PR20_ne_couvre_pas_l_intra_ecriture`] L'énoncé : sans créance de `a` sur lui-même, pas de lien de `a` à `a`. Il ne dit pas que l'intra-écriture est hors de portée ; il en exhibe l'absence sur la diagonale.
theorem sans_creance_sur_soi_pas_de_lien_a_soi (c : Creance) (a : Actor)
    (h : c a a = false) : lien c a a = false := by
  unfold lien; simp [h]

/-- **PR-20 ne juge pas le montant.** L'accord des deux registres porte
    sur l'existence du lien ; la valeur portée hors du point plein est
    libre — voir `accord_sur_l_existence_pas_sur_la_valeur`, qui en
    exhibe deux. Le théorème ci-dessous en tire la conséquence
    opératoire : une même relation de créance admet **plusieurs**
    registres augmentés cohérents.

    [C-8 — 28/09/2026] Renommé (ex-`PR20_admet_plusieurs_evaluations`) : l'énoncé
    est une **lecture** (`rfl`) — les deux écritures ont le même socle. La
    pluralité des évaluations est portée par `accord_sur_l_existence_pas_sur_la_valeur`. -/
theorem les_deux_registres_augmentes_ont_le_meme_socle (c : Creance) :
    (registreAugmenteDe c).socle = (registreAugmenteBis c).socle := rfl

/-- **Témoin discriminant** (R-7, 28/09/2026) des lectures de `lien` et de
    `registreCommunalite` — `sans_creance_aucun_lien`, `absence_n_est_pas_lien_nul`,
    `sans_creance_sur_soi_pas_de_lien_a_soi` : sur une créance non vide, les deux
    fonctions rendent l'**autre** valeur (lien `true`, mention `inscrit`). -/
theorem lien_temoin_discriminant :
    lien (fun x y => x == "A" && y == "B") "A" "B" = true
    ∧ registreCommunalite (fun x y => x == "A" && y == "B") "A" "B" = MentionCom.inscrit := by
  constructor <;> decide

end ProfRegPR20
