/-
  PR-10 · `seuil_valuatif_must_declare_status`
  ============================================

  Spécification d'origine (MRC v5.6) :
    · `MRC_v5.6_ProfReg_Consolide.md` §4, ligne PR-10 —
      « toute mobilisation d'une primitive `seuil-valuatif` déclare le
        quadruplet "statut du seuil" (généralisation hors-F8 de PR-1) »
    · `MRC_v5.6_Annexe_Methodologique.md` §A.14 — règle R0-bis,
      définitions §A.14.1, critère de séparabilité §A.14.2,
      table de typage §A.14.7, conditions de réfutation §A.14.8
    · Attribut `charge_valuative` acté en NT-ARCH §2bis (4 juillet 2026).

  Porteur : Pierre Musseau. Écrit le 7 septembre 2026.

  Ce fichier ne dépend pas de Mathlib : Lean 4 pur.

  DÉDUPLIQUÉ le 7 septembre 2026 au soir (tâche 3quinquies).
  `Actor`, `RegimeUsage` et `StatutSeuil` dupliquaient celles de
  `LotL2_PR2_PR14.lean` ; elles en sont désormais importées. Les deux
  copies étaient identiques, mais rien ne garantissait qu'elles le
  restent — et trois autres copies du set avaient déjà dérivé.
-/

import ProfReg.LotL2_PR2_PR14

namespace ProfRegPR10

open ProfRegLot

/-! ## 1. L'attribut de Couche 0 qui rend PR-10 quantifiable

`charge_valuative` (NT-ARCH §2bis, Annexe §A.14.1) est le discriminant
sans lequel PR-10 n'a pas d'objet : c'est lui qui désigne *quelles*
primitives sont concernées. Le set le déclare à deux valeurs ; la table
§A.14.7 en produit une troisième de fait — sept cas
`[CHARGE VALUATIVE MIXTE — à trancher par le porteur]` — que l'on
inscrit ici explicitement plutôt que de la dissimuler. -/

inductive ChargeValuative where
  | relationnelle
  | seuilValuatif
  | mixte
  deriving DecidableEq, Repr

/-- §A.14.7 : « Les cas mixtes sont marqués `[CHARGE VALUATIVE MIXTE]`
    et traités, **par prudence**, comme `seuil-valuatif`. »
    La prudence est donc une fonction, non une opinion. -/
def apresPrudence : ChargeValuative → ChargeValuative
  | ChargeValuative.mixte => ChargeValuative.seuilValuatif
  | c => c

/-! `RegimeUsage`, `UsageAgregat` et `StatutSeuil` — le **quintuplet**
« statut du seuil » du §A.14.1 — viennent de `ProfReg.LotL2_PR2_PR14`,
où ils sont déclarés une seule fois pour les deux fichiers.

Le cinquième terme, `usageAgregat`, est versé le 8 septembre 2026
(option D). Il est traité au §7 ci-dessous. -/

/-- Architecture §8.1.1 — axe **orthogonal** au précédent (§A.14.6). -/
inductive Usage where
  | u1 | u2 | u3
  deriving DecidableEq, Repr

structure Primitive where
  nom : String
  charge : ChargeValuative
  deriving Repr

/-- Une mobilisation, c'est-à-dire un **usage inscrit** d'une primitive.
    PR-10 porte sur les mobilisations, pas sur les primitives : une même
    primitive peut être mobilisée normativement ici et descriptivement là. -/
structure Mobilisation where
  primitive : Primitive
  usage : Usage
  statut : Option StatutSeuil
  marqueurValuationSuspendue : Bool
  referenceDeclaree : Option String

/-! ## 2. La règle R0-bis comme condition de bonne formation

Deux clauses, et la seconde est ce qui empêche PR-10 d'être creux.
§A.14.3 exige le quadruplet des `seuil-valuatif` ; §A.14.1 *in fine*
dit que « les primitives `relationnelle` restent d'usage descriptif
libre **à condition de déclarer la référence** ». Deux exigences
distinctes, sur deux classes disjointes. -/

def BienFormee (m : Mobilisation) : Prop :=
  (apresPrudence m.primitive.charge = ChargeValuative.seuilValuatif →
      m.statut ≠ none)
  ∧ (apresPrudence m.primitive.charge = ChargeValuative.relationnelle →
      m.referenceDeclaree ≠ none)

/-! ## 3. PR-10 -/

/-- **PR-10.** Toute mobilisation bien formée d'une primitive
    `seuil-valuatif` exhibe le quadruplet « statut du seuil ». -/
theorem seuil_valuatif_must_declare_status
    (m : Mobilisation) (h_bf : BienFormee m)
    (h_sv : m.primitive.charge = ChargeValuative.seuilValuatif) :
    ∃ s, m.statut = some s := by
  have h : m.statut ≠ none := by
    apply h_bf.1
    rw [h_sv]
    rfl
  cases hm : m.statut with
  | none => exact absurd hm h
  | some s => exact ⟨s, rfl⟩

/-- **Le pas de prudence est démontré, non supposé.** Un cas
    `[CHARGE VALUATIVE MIXTE]` non tranché par le porteur est soumis à
    la même exigence qu'un `seuil-valuatif` avéré. C'est la lecture
    stricte du §A.14.7, et elle a un coût : sept primitives sont
    contraintes sans que le porteur ait tranché. -/
theorem mixte_traite_comme_seuil_valuatif
    (m : Mobilisation) (h_bf : BienFormee m)
    (h_m : m.primitive.charge = ChargeValuative.mixte) :
    ∃ s, m.statut = some s := by
  have h : m.statut ≠ none := by
    apply h_bf.1
    rw [h_m]
    rfl
  cases hm : m.statut with
  | none => exact absurd hm h
  | some s => exact ⟨s, rfl⟩

/-- **PR-10 ne vaut pas partout — et c'est ce qui lui donne un contenu.**
    Il existe des mobilisations bien formées sans quadruplet : celles des
    primitives `relationnelle`, qui ne doivent qu'une référence déclarée.

    C'est le test oxygène/allumette appliqué au set lui-même : une règle
    qui s'appliquerait à toute primitive n'expliquerait rien. Sans ce
    contre-exemple, PR-10 serait indiscernable d'une obligation
    universelle de déclaration — et l'attribut `charge_valuative`
    serait décoratif. -/
theorem PR10_ne_vaut_pas_pour_les_relationnelles :
    ∃ m : Mobilisation, BienFormee m ∧ m.statut = none := by
  -- [D-3 CLOSE LE 27/09/2026 — décision de porteur] témoin remplacé : `type_capabilité_centrale`
  -- est scindé depuis le 11/09 (NT-G7 §3.1ter) ; `capabilite_individuelle` est la moitié
  -- restée `relationnelle`, à liste de référence déclarée (Nussbaum 2000, p. 76-78).
  refine ⟨{ primitive := { nom := "capabilite_individuelle"
                         , charge := ChargeValuative.relationnelle }
          , usage := Usage.u1
          , statut := none
          , marqueurValuationSuspendue := false
          , referenceDeclaree := some "Nussbaum 2000, liste p. 76-78" }, ?_, rfl⟩
  constructor
  · intro h; exact absurd h (by decide)
  · intro _; simp

/-- **Après le pas de prudence, le typage est exactement binaire.**
    Conséquence directe : une valuation *émique* — portée par le
    collectif enquêté, ni suspendue ni endossée par le modèle, cas
    `travail_bien_fait` du §A.14.7 — n'a pas de classe propre. Elle est
    nécessairement rangée sous l'une des deux, et le set le sait :
    « le typage binaire est **suffisant mais à surveiller** ». -/
theorem typage_binaire_apres_prudence (c : ChargeValuative) :
    apresPrudence c = ChargeValuative.relationnelle ∨
    apresPrudence c = ChargeValuative.seuilValuatif := by
  cases c with
  | relationnelle => exact Or.inl rfl
  | seuilValuatif => exact Or.inr rfl
  | mixte => exact Or.inr rfl

/-! ## 4. La suspension de valuation

§A.14.1 : « Ce n'est **ni l'endossement ni l'absence** de valuation :
c'est sa mise entre parenthèses **tracée**. » Cette phrase est un énoncé
à deux exclusions, et c'est sous cette forme qu'on la démontre. -/

def SuspensionBienDeclaree (m : Mobilisation) : Prop :=
  ∃ s, m.statut = some s
     ∧ s.regimeUsage = RegimeUsage.descriptifSuspendu
     ∧ m.marqueurValuationSuspendue = true

/-- **La suspension n'est ni l'absence, ni l'endossement.**
    Les deux exclusions du §A.14.1, démontrées ensemble. -/
theorem suspension_ni_absence_ni_endossement
    (m : Mobilisation) (h : SuspensionBienDeclaree m) :
    m.statut ≠ none ∧
    (∀ s, m.statut = some s → s.regimeUsage ≠ RegimeUsage.normatif) := by
  obtain ⟨s, hs, hreg, _⟩ := h
  constructor
  · rw [hs]; simp
  · intro t ht
    have hst : s = t := Option.some.inj (hs.symm.trans ht)
    rw [← hst, hreg]
    exact fun h' => RegimeUsage.noConfusion h'

/-- CONVENTION PR10-a — lecture déclarée, non démontrée : « déclencher
    une règle R-* » est identifié au régime d'usage normatif. C'est ma
    traduction de « Aucune règle R-* n'est alors déclenchée » (R0-bis) ;
    le set ne définit pas le déclenchement au niveau où PR-10 opère. -/
def DeclencheRegle (m : Mobilisation) : Prop :=
  ∃ s, m.statut = some s ∧ s.regimeUsage = RegimeUsage.normatif

/-- **R0-bis, seconde moitié.** Une suspension correctement déclarée ne
    déclenche aucune règle. Sous la convention PR10-a. -/
theorem suspension_ne_declenche_aucune_regle
    (m : Mobilisation) (h : SuspensionBienDeclaree m) :
    ¬ DeclencheRegle m := by
  obtain ⟨s, hs, hreg, _⟩ := h
  rintro ⟨t, ht, hnorm⟩
  have hst : s = t := Option.some.inj (hs.symm.trans ht)
  rw [hst, hnorm] at hreg
  exact RegimeUsage.noConfusion hreg

/-! ## 5. Orthogonalité des deux axes (§A.14.6)

« Les deux axes se croisent (on peut faire un usage descriptif-suspendu
en Usage 2) ; les confondre ("descriptif = Usage 1") est un
`[CHANGEMENT DE BASE NON TRACÉ]`. »

L'orthogonalité se démontre en exhibant les deux croisements que la
confusion interdirait. -/

theorem orthogonalite_charge_valuative_usage :
    (∃ m : Mobilisation, m.usage = Usage.u2 ∧ SuspensionBienDeclaree m) ∧
    (∃ m : Mobilisation, m.usage = Usage.u1 ∧ DeclencheRegle m) := by
  constructor
  -- [D-3 CLOSE LE 27/09/2026 — second témoin, décision de porteur] `capabilité_plancher_menacée` est
  -- scindé depuis le 11/09 (NT-G7 §3.1) en `capabilite_menacee` + `seuil_franchi` ;
  -- le seuil valuatif est la moitié booléenne, `seuil_franchi`, de source G-JUSTICE.
  · refine ⟨{ primitive := { nom := "seuil_franchi"
                           , charge := ChargeValuative.seuilValuatif }
            , usage := Usage.u2
            , statut := some { source := "NT-G7 (G-JUSTICE) ; capabilité nommée par capabilite_menacee"
                             , conventionMesure := "plancher déclaré"
                             , regimeUsage := RegimeUsage.descriptifSuspendu
                             , porteurDeclaration := "chercheur-pilote"
                             , usageAgregat := UsageAgregat.sansAgregat }
            , marqueurValuationSuspendue := true
            , referenceDeclaree := none }, rfl, ?_⟩
    exact ⟨_, rfl, rfl, rfl⟩
  · refine ⟨{ primitive := { nom := "seuil_degredation_irréversible"
                           , charge := ChargeValuative.seuilValuatif }
            , usage := Usage.u1
            , statut := some { source := "NT-G5"
                             , conventionMesure := "seuil jonasien"
                             , regimeUsage := RegimeUsage.normatif
                             , porteurDeclaration := "porteur"
                             , usageAgregat := UsageAgregat.sansAgregat }
            , marqueurValuationSuspendue := false
            , referenceDeclaree := none }, rfl, ?_⟩
    exact ⟨_, rfl, rfl⟩

/-! ## 6. Ce que PR-10 ne démontre pas

§A.14.8(1) énonce la condition de réfutation de R0-bis : la règle tombe
si l'on exhibe une primitive `seuil-valuatif` dont la suspension la vide
de tout contenu descriptif. Cette condition est **sémantique** : elle
porte sur ce que la primitive décrit, non sur la forme de son
inscription. PR-10 est formel : il porte sur la forme.

Le théorème suivant inscrit cet écart au lieu de le laisser implicite. -/

/-- **PR-10 ne prouve pas la séparabilité.** Pour tout prédicat de
    séparabilité, il existe une mobilisation bien formée dont la
    primitive ne le satisfait pas. Autrement dit : l'inscription
    conforme ne vaut pas certificat de séparabilité, et le critère
    §A.14.2 reste à instruire primitive par primitive, hors de Lean. -/
theorem PR10_ne_prouve_pas_la_separabilite :
    ∀ (Sep : Primitive → Prop) (p : Primitive), ¬ Sep p →
      ∃ m : Mobilisation, m.primitive = p ∧ BienFormee m ∧ ¬ Sep m.primitive := by
  -- [B-7, 28/09/2026] Reformulé : l'ancien énoncé était existentiel, avec le
  -- prédicat vide pour témoin (forme 6), alors que la docstring dit « pour tout
  -- prédicat ». L'énoncé est maintenant universel : toute primitive, quelle que
  -- soit sa charge, se mobilise de façon bien formée — la conformité de forme ne
  -- filtre donc aucun prédicat de séparabilité.
  intro Sep p hp
  refine ⟨{ primitive := p, usage := Usage.u1
          , statut := some { source := "source déclarée"
                           , conventionMesure := "convention déclarée"
                           , regimeUsage := RegimeUsage.descriptifSuspendu
                           , porteurDeclaration := "porteur"
                           , usageAgregat := UsageAgregat.sansAgregat }
          , marqueurValuationSuspendue := true
          , referenceDeclaree := some "référence déclarée" }, rfl, ?_, hp⟩
  exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩

/-! ## 7. Le cinquième terme — ce que l'agrégat sert à établir

*Versé le 8 septembre 2026, option D. Décision de porteur.*

Le quadruplet devient **quintuplet**. Le terme ajouté répond à une
question que le set ne posait nulle part :

> **Quand vous dites que le seuil est atteint, l'avez-vous établi
> cas par cas — ou par une somme ?**

**Ancrage.** André, M. & Gosseries, A., *La Justice climatique*, PUF
« Que sais-je ? », 2024, ch. I §II : l'approche par les droits
fondamentaux « rejette l'agrégation des intérêts qui prévaut dans
l'analyse coût-bénéfice » ET « n'empêche pas, une fois le seuil de
dignité atteint pour tous, de chercher ensuite à maximiser le
bien-être agrégé ». Agrégation **exclue pour constater le
franchissement**, **permise au-dessus**. [VÉRIFIÉ sur source primaire]

**Option D — déclarer, non interdire.** Le MRC n'arbitre pas entre les
théories de la justice : il oblige à déclarer laquelle s'applique
(NT-G2 §7). La source ne couvre que le cas suffisantiste ; étendre
l'INTERDICTION à tout principe serait un [ENGAGEMENT SANS SYMÉTRIE].
Étendre la DÉCLARATION est un choix de forme, assumé comme tel.

**Ce qui suit doit trier.** Un champ obligatoire vrai par construction
du typage ne se prouve pas — c'est ce qui a produit CONV-1 à CONV-4 le
7 septembre. La part déclarative est donc inscrite comme **CONV-9** ;
les théorèmes ci-dessous sont ceux qui discriminent. -/

/-- Le quintuplet est complètement déclaré : le cinquième terme est
    renseigné autrement que par le défaut. -/
def QuintupletDeclare (m : Mobilisation) : Prop :=
  ∃ s, m.statut = some s ∧ s.usageAgregat ≠ UsageAgregat.nonDeclare

/-- **Le silence ne vaut pas déclaration.** Une mobilisation dont le
    cinquième terme est `nonDeclare` n'a pas déclaré son quintuplet —
    quand bien même le champ est présent et le reste du statut complet.
    Homologue de `nonDeclare_ne_vaut_pas_permission` (PR-17). -/
theorem usage_agregat_non_declare_n_est_pas_une_declaration
    (m : Mobilisation) (s : StatutSeuil)
    (h : m.statut = some s)
    (h_nd : s.usageAgregat = UsageAgregat.nonDeclare) :
    ¬ QuintupletDeclare m := by
  intro ⟨s', hs', hne⟩
  rw [h] at hs'
  have : s' = s := by injection hs' with h'; exact h'.symm
  subst this
  exact hne h_nd

/-! Le linter `unusedVariables` a écarté ici une première rédaction —
`seuil_valuatif_must_declare_quintuplet` — dont les hypothèses
`BienFormee` et `seuil-valuatif` étaient inertes : elle reprenait sa
conclusion en hypothèse. Troisième forme de sur-revendication
(NT-ARCH §8ter), attrapée par la deuxième. Elle est remplacée par
l'énoncé qui **prouve le trou** au lieu de le supposer. -/

/-- **Le quadruplet ne borne pas le quintuplet.** Il existe une
    mobilisation `seuil-valuatif` parfaitement bien formée au sens de
    R0-bis — statut présent, quatre termes renseignés — dont le
    cinquième terme n'est **pas** déclaré.

    C'est exactement le trou que CONV-9 ferme, et il est ici démontré
    plutôt que postulé. Même figure que `PR14_ne_borne_pas_l_attribution`
    pour PR-3 : l'obligation nouvelle est motivée par un théorème, non
    par une intuition. -/
theorem BienFormee_ne_borne_pas_le_quintuplet :
    ∃ m : Mobilisation,
      m.primitive.charge = ChargeValuative.seuilValuatif
      ∧ BienFormee m ∧ ¬ QuintupletDeclare m := by
  refine ⟨{ primitive := { nom := "seuil hérité d'un modèle"
                         , charge := ChargeValuative.seuilValuatif }
          , usage := Usage.u1
          , statut := some { source := "corpus déclaré"
                           , conventionMesure := "convention déclarée"
                           , regimeUsage := RegimeUsage.normatif
                           , porteurDeclaration := "porteur déclaré"
                           , usageAgregat := UsageAgregat.nonDeclare }
          , marqueurValuationSuspendue := false
          , referenceDeclaree := none }, rfl, ?_, ?_⟩
  · constructor
    · intro _; simp
    · intro h; exact absurd h (by decide)
  · exact usage_agregat_non_declare_n_est_pas_une_declaration _ _ rfl rfl

/-! ### 7.1 L'axe est nouveau — il ne se déduit pas de `regimeUsage`

Le cinquième terme serait inutile s'il se lisait dans le troisième.
On exhibe les quatre croisements que la confusion interdirait :
un seuil **normatif** peut être établi par agrégat ou sans agrégat ;
un seuil **descriptif-suspendu** aussi. -/

def statutTypique (r : RegimeUsage) (u : UsageAgregat) : StatutSeuil :=
  { source := "corpus déclaré"
  , conventionMesure := "convention déclarée"
  , regimeUsage := r
  , porteurDeclaration := "porteur déclaré"
  , usageAgregat := u }

/-- **Orthogonalité du cinquième terme.** Les quatre combinaisons
    `regimeUsage × usageAgregat` sont réalisables. Le cinquième terme
    n'est donc pas dérivable du troisième — et les fusionner dans une
    seule énumération, comme je l'avais d'abord proposé, aurait été un
    `[CHANGEMENT DE BASE NON TRACÉ]`.

    Même figure que `orthogonalite_charge_valuative_usage` ci-dessus,
    sur un troisième axe. -/
theorem orthogonalite_usage_agregat_regime_usage :
    (statutTypique RegimeUsage.normatif UsageAgregat.constatation).regimeUsage
      = RegimeUsage.normatif
  ∧ (statutTypique RegimeUsage.normatif UsageAgregat.sansAgregat).regimeUsage
      = RegimeUsage.normatif
  ∧ (statutTypique RegimeUsage.descriptifSuspendu UsageAgregat.constatation).regimeUsage
      = RegimeUsage.descriptifSuspendu
  ∧ (statutTypique RegimeUsage.descriptifSuspendu UsageAgregat.sansAgregat).regimeUsage
      = RegimeUsage.descriptifSuspendu
  ∧ (statutTypique RegimeUsage.normatif UsageAgregat.constatation).usageAgregat
      ≠ (statutTypique RegimeUsage.normatif UsageAgregat.sansAgregat).usageAgregat :=
  ⟨rfl, rfl, rfl, rfl, by decide⟩

/-! ### 7.2 Gardes — l'option D déclare, elle n'interdit pas -/

/-- **`constatation` reste licite.** Une mobilisation qui déclare
    établir le franchissement par agrégat a un quintuplet déclaré et
    est bien formée. Sans cet énoncé, le cinquième terme se lirait
    comme une interdiction déguisée de l'agrégation. -/
def mobilisationParConstatation : Mobilisation :=
  { primitive := { nom := "seuil de réchauffement 1,5 °C"
                 , charge := ChargeValuative.seuilValuatif }
  , usage := Usage.u1
  , statut := some (statutTypique RegimeUsage.normatif UsageAgregat.constatation)
  , marqueurValuationSuspendue := false
  , referenceDeclaree := none }

theorem constatation_reste_licite :
    BienFormee mobilisationParConstatation
    ∧ QuintupletDeclare mobilisationParConstatation := by
  constructor
  · constructor
    · intro _; simp [mobilisationParConstatation]
    · intro h; exact absurd h (by decide)
  · exact ⟨_, rfl, by decide⟩

/-- **PR-10 ne juge pas l'usage de l'agrégat.** Deux mobilisations
    peuvent différer sur le seul cinquième terme et être toutes deux
    bien formées et complètement déclarées. Le terme **enregistre**,
    il ne classe pas. -/
def mobilisationSansAgregat : Mobilisation :=
  { mobilisationParConstatation with
    statut := some (statutTypique RegimeUsage.normatif UsageAgregat.sansAgregat) }

theorem PR10_ne_juge_pas_l_usage_de_l_agregat :
    (BienFormee mobilisationParConstatation ∧ QuintupletDeclare mobilisationParConstatation)
  ∧ (BienFormee mobilisationSansAgregat ∧ QuintupletDeclare mobilisationSansAgregat) := by
  refine ⟨constatation_reste_licite, ?_, ?_⟩
  · constructor
    · intro _; simp [mobilisationSansAgregat, mobilisationParConstatation]
    · intro h; exact absurd h (by decide)
  · exact ⟨_, rfl, by decide⟩

/-- **Le cinquième terme ne dit pas si le seuil est bon.** Il dit
    comment on établit qu'il est franchi. Les deux mobilisations
    ci-dessus portent le même seuil, la même source, la même convention
    de mesure et le même porteur ; elles ne diffèrent que sur ce que la
    somme sert à établir. -/
theorem le_cinquieme_terme_ne_touche_pas_au_seuil :
    mobilisationParConstatation.primitive = mobilisationSansAgregat.primitive
  ∧ (statutTypique RegimeUsage.normatif UsageAgregat.constatation).source
      = (statutTypique RegimeUsage.normatif UsageAgregat.sansAgregat).source :=
  ⟨rfl, rfl⟩

/-! ## Témoins D-13 (règle NT-ARCH §8ter-bis, R-2) — versés le 28/09/2026

`seuil_valuatif_must_declare_status`, `mixte_traite_comme_seuil_valuatif`
(clause 1 de `BienFormee`), `suspension_ni_absence_ni_endossement` et
`suspension_ne_declenche_aucune_regle` (`SuspensionBienDeclaree`) sont des
lectures (R-3). Témoins bien formés : `constatation_reste_licite`,
`orthogonalite_charge_valuative_usage` ; témoins mal formés ci-dessous. -/

/-- Témoin discriminant de la clause 1 de `BienFormee` : seuil valuatif sans
    statut, référence déclarée (clause 2 satisfaite). -/
theorem PR10_clause1_temoin_mal_forme :
    ∃ m : Mobilisation,
      m.primitive.charge = .seuilValuatif ∧ m.statut = none
      ∧ m.referenceDeclaree ≠ none ∧ ¬ BienFormee m :=
  ⟨{ primitive := { nom := "s", charge := .seuilValuatif }, usage := .u1,
     statut := none, marqueurValuationSuspendue := false,
     referenceDeclaree := some "r" },
   rfl, rfl, (fun h => nomatch h), fun h => h.1 rfl rfl⟩

/-- Témoin mal formé de `SuspensionBienDeclaree` : marqueur levé, statut absent. -/
theorem PR10_suspension_temoin_mal_forme :
    ∃ m : Mobilisation, m.marqueurValuationSuspendue = true
      ∧ ¬ SuspensionBienDeclaree m :=
  ⟨{ primitive := { nom := "s", charge := .seuilValuatif }, usage := .u2,
     statut := none, marqueurValuationSuspendue := true,
     referenceDeclaree := none },
   rfl, (fun ⟨_, hs, _⟩ => nomatch hs)⟩

end ProfRegPR10
