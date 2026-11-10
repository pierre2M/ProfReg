/-
  PR-3 · `attribuee_seuil_declare_required` — version paramétrée
  ==============================================================

  Spécification d'origine (MRC v5.6) :
    · `MRC_v5.6_NT-ARCH_Architecture_Couches0-3.md` §7bis —
      invariant ACT-ARCH-001, acté le 3 juillet 2026 :
      « La combinaison C-STATUT-DETTE = ATTRIBUEE avec
        seuilentreecommunautemorale = NONDECLARE est interdite »
      et sa **contrepartie réfutable** :
      « L'invariant est révisable vers un repli "re-déclaration à
        échéance" (plutôt qu'"à l'attribution") si le cas "seuil
        matériellement non déterminable à l'instant de l'attribution"
        se révèle empiriquement récurrent. »
    · §3 — énumération C-STATUT-DETTE ; §4 — machine d'états ;
      §5.1 — seuilentreecommunautemorale ∈ {SENTIENCE,
      FINALITEIMMANENTE, NONDECLARE}
    · `MRC_v5.6_Annexe_Methodologique.md` §A.14.7 — la ligne
      « Architecture §5.1 » type `seuilentreecommunautemorale` comme
      **seuil-valuatif** : PR-10 s'y applique.

  DÉCISION DE PORTEUR du 7 septembre 2026 — **option C**.
  L'invariant n'est pas écrit dans l'un des deux régimes temporels :
  il est écrit **paramétré par l'échéance de déclaration**, et l'on
  démontre que le régime strict de §7bis en est l'instance où
  l'échéance vaut l'instant de l'attribution. La clause de révision
  de §7bis devient ainsi **exécutable** — changer de régime est
  changer un paramètre, non réécrire le set — sans préempter le
  constat empirique de récurrence auquel §7bis la conditionne.
  Voir `Decision_PR3_2026-09-07.md`.

  CORRIGÉ le 7 septembre 2026 au soir — décision du porteur.
  La première rédaction déclarait un `StatutDette` à QUATRE
  constructeurs, dont `critique`, fusionnant deux types du set en un
  seul. C'était une erreur de lecture : NT-G2 §3.1, note de
  déclenchement, écrit trois fois « niveau CRITIQUE » et jamais
  « statut », et `V4Verification.lean` type la machine d'états comme
  `transition_valide : StatutDette → NiveauRIA` -- NiveauRIA
  signifiant *niveau de R-Interdit-Absolu*. CRITIQUE est un niveau de
  déclenchement de la règle, non un état de la dette.
  Les types viennent désormais de `ProfReg.Primitives`, où ils sont
  déclarés une seule fois pour tout le set (tâche 3quinquies).

  Porteur : Pierre Musseau. Écrit le 7 septembre 2026.
  Lean 4 pur, sans Mathlib. Dépend de `ProfReg.Primitives` et de
  `ProfReg.PR10_StatutSeuil` (sans Mathlib l'un et l'autre).
-/

import ProfReg.Primitives
import ProfReg.PR10_StatutSeuil

namespace ProfRegPR3

/-! ## 1. Les primitives du set

Elles ne sont plus recopiées : elles viennent de `ProfReg.Primitives`,
qui les déclare une fois pour tout le set. `SeuilCommunauteMorale`
(NT-ARCH §5.1), `StatutDette` (§3) et `NiveauRIA` (§4) y sont, ainsi
que la machine d'états `transition_valide`. -/

open ProfReg

/-! ## 2. Le paramètre : l'échéance de déclaration

C'est la seule chose que ce fichier ajoute au set, et c'est la
décision d'option C. `aLAttribution` est le régime de §7bis ;
`aDate` est son repli ; `nonNommee` n'est pas un régime que l'on
propose — c'est le cas dégénéré qu'il faut pouvoir nommer pour
démontrer qu'il ne vaut rien (§4). -/

inductive Echeance where
  | aLAttribution
  | aDate (t : Nat)
  | nonNommee
  deriving Repr

/-- Le temps est ici un simple compteur d'ordre. Aucune sémantique
    calendaire n'est supposée : seule compte la comparaison. -/
structure Dette where
  statut : StatutDette
  seuil : SeuilCommunauteMorale
  tAttribution : Nat
  /-- Instant auquel le seuil a été déclaré. `none` = jamais. -/
  tDeclarationSeuil : Option Nat

def SeuilDeclare (d : Dette) : Prop :=
  d.seuil ≠ SeuilCommunauteMorale.nonDeclare

/-- « Déclaré dans les temps », selon le régime. La troisième
    branche est vraie de tout : c'est exactement ce qui fait qu'une
    échéance non nommée n'exige rien. -/
def DeclareDansLesTemps (d : Dette) : Echeance → Prop
  | Echeance.aLAttribution =>
      ∃ t, d.tDeclarationSeuil = some t ∧ t ≤ d.tAttribution
  | Echeance.aDate T =>
      ∃ t, d.tDeclarationSeuil = some t ∧ t ≤ T
  | Echeance.nonNommee => True

/-- **ACT-ARCH-001, paramétré.** Toute dette passée à ATTRIBUEE
    porte un seuil déclaré, et l'a déclaré dans les temps du régime
    en vigueur. Avec `e = aLAttribution`, c'est la lettre de §7bis. -/
def ACT_ARCH_001 (e : Echeance) (d : Dette) : Prop :=
  d.statut = StatutDette.attribuee → SeuilDeclare d ∧ DeclareDansLesTemps d e

/-! ## 3. PR-3 -/

/-- **PR-3 — `attribuee_seuil_declare_required`.** La combinaison
    interdite est impossible : sous ACT-ARCH-001, aucune dette
    ATTRIBUEE ne porte un seuil NONDECLARE.

    Le théorème vaut **pour tout régime d'échéance** : ce qui est
    interdit l'est dans les deux régimes. C'est le premier résultat
    de la paramétrisation — le repli n'affaiblit pas l'interdiction
    elle-même, seulement son instant. -/
theorem attribuee_seuil_declare_required
    (e : Echeance) (d : Dette) (h : ACT_ARCH_001 e d)
    (h_att : d.statut = StatutDette.attribuee)
    (h_nd : d.seuil = SeuilCommunauteMorale.nonDeclare) : False := by
  exact (h h_att).1 h_nd

/-- Corollaire de forme positive, plus commode à l'usage. -/
theorem attribution_exige_un_seuil_declare
    (e : Echeance) (d : Dette) (h : ACT_ARCH_001 e d)
    (h_att : d.statut = StatutDette.attribuee) :
    d.seuil = SeuilCommunauteMorale.sentience ∨
    d.seuil = SeuilCommunauteMorale.finaliteImmanente := by
  have h_sd : SeuilDeclare d := (h h_att).1
  cases hs : d.seuil with
  | sentience => exact Or.inl rfl
  | finaliteImmanente => exact Or.inr rfl
  | nonDeclare => exact absurd hs h_sd

/-! ## 4. Ce que la paramétrisation démontre

Trois théorèmes. Le premier rend la clause de révision de §7bis
exécutable ; les deux suivants disent ce que le repli coûte, et à
quelle condition il ne dégénère pas. -/

/-- **Le régime strict est l'instance du repli où l'échéance vaut
    l'instant de l'attribution.**

    C'est le théorème qui justifie l'option C : passer de §7bis à
    son repli n'est pas réécrire l'invariant, c'est déplacer un
    paramètre. La clause de révision cesse d'être une intention. -/
theorem stricte_est_instance_du_repli (d : Dette)
    (h : ACT_ARCH_001 Echeance.aLAttribution d) :
    ACT_ARCH_001 (Echeance.aDate d.tAttribution) d := by
  intro h_att
  obtain ⟨h_sd, t, ht, hle⟩ := h h_att
  exact ⟨h_sd, t, ht, hle⟩

/-- **Et réciproquement.** Les deux régimes coïncident exactement
    lorsque l'échéance est l'instant de l'attribution : ce n'est pas
    une inclusion commode, c'est une identité. -/
theorem repli_a_l_instant_d_attribution_est_strict (d : Dette)
    (h : ACT_ARCH_001 (Echeance.aDate d.tAttribution) d) :
    ACT_ARCH_001 Echeance.aLAttribution d := by
  intro h_att
  obtain ⟨h_sd, t, ht, hle⟩ := h h_att
  exact ⟨h_sd, t, ht, hle⟩

/-- **Sans échéance nommée, le repli ne contraint plus rien.**
    On exhibe une dette ATTRIBUEE, portant un seuil, dont le seuil
    n'a **jamais** été déclaré — et qui satisfait néanmoins
    ACT-ARCH-001 sous échéance non nommée.

    C'est le théorème qui rend l'échéance **obligatoire** et non
    recommandée : « à déclarer plus tard » sans date est
    NONDECLARE sous un autre nom, avec en prime une obligation
    devenue opposable. -/
theorem repli_sans_echeance_degenere :
    ∃ d : Dette, ACT_ARCH_001 Echeance.nonNommee d
               ∧ d.statut = StatutDette.attribuee
               ∧ d.tDeclarationSeuil = none := by
  refine ⟨{ statut := StatutDette.attribuee
          , seuil := SeuilCommunauteMorale.sentience
          , tAttribution := 0
          , tDeclarationSeuil := none }, ?_, rfl, rfl⟩
  intro _
  refine ⟨?_, trivial⟩
  intro h
  exact SeuilCommunauteMorale.noConfusion h

/-- **Une échéance nommée, elle, exige une date.** Le contraste avec
    le théorème précédent est tout le contenu de la condition
    « l'échéance doit être obligatoire ». -/
theorem echeance_nommee_exige_une_date
    (T : Nat) (d : Dette) (h : ACT_ARCH_001 (Echeance.aDate T) d)
    (h_att : d.statut = StatutDette.attribuee) :
    ∃ t, d.tDeclarationSeuil = some t ∧ t ≤ T :=
  (h h_att).2

/-! ## 5. Ce que le choix du régime change réellement

Les deux théorèmes suivants sont symétriques et se lisent ensemble :
ils disent, l'un et l'autre, la même chose vue des deux bords. -/

/-- **Le régime strict interdit toute déclaration postérieure à
    l'attribution.** C'est sa force, et c'est son coût : un seuil
    matériellement indéterminable à cet instant rend l'attribution
    impossible. -/
theorem stricte_interdit_declaration_posterieure
    (d : Dette) (h : ACT_ARCH_001 Echeance.aLAttribution d)
    (h_att : d.statut = StatutDette.attribuee)
    (t : Nat) (ht : d.tDeclarationSeuil = some t) :
    t ≤ d.tAttribution := by
  obtain ⟨_, u, hu, hle⟩ := h h_att
  have : u = t := Option.some.inj (hu.symm.trans ht)
  exact this ▸ hle

/-- **Le repli à échéance autorise l'attribution avant le règlement
    du seuil.** On exhibe une dette attribuée à l'instant 1, dont le
    seuil n'est déclaré qu'à l'instant 5, sous une échéance fixée à
    10 — conforme au repli, interdite par le régime strict.

    C'est le cas que §7bis avait en vue : « seuil matériellement non
    déterminable à l'instant de l'attribution ». -/
theorem repli_autorise_l_attribution_avant_declaration :
    ∃ (T : Nat) (d : Dette),
      ACT_ARCH_001 (Echeance.aDate T) d
      ∧ d.statut = StatutDette.attribuee
      ∧ ¬ ACT_ARCH_001 Echeance.aLAttribution d := by
  refine ⟨10, { statut := StatutDette.attribuee
              , seuil := SeuilCommunauteMorale.finaliteImmanente
              , tAttribution := 1
              , tDeclarationSeuil := some 5 }, ?_, rfl, ?_⟩
  · intro _
    refine ⟨?_, 5, rfl, by decide⟩
    intro h; exact SeuilCommunauteMorale.noConfusion h
  · intro h
    obtain ⟨_, t, ht, hle⟩ := h rfl
    have : t = 5 := Option.some.inj ht.symm
    rw [this] at hle
    exact absurd hle (by decide)

/-! ## 6. La machine d'états du set, et l'enchaînement qu'elle produit

**Rejoué le 7 septembre 2026 sur la machine d'états du set**, après
correction de la fusion `StatutDette` / `NiveauRIA`.

NT-ARCH §4 : `transition_valide : StatutDette → NiveauRIA`. CRITIQUE
est un **niveau de déclenchement de R-INTERDIT-ABSOLU**, atteignable
depuis le seul statut ATTRIBUEE — `transition_valide nonAttribuee
critique` et `transition_valide enDeliberation critique` valent tous
deux `False`.

Composée avec ACT-ARCH-001, cette règle produit un effet que ni l'une
ni l'autre ne vise. On le démontre plutôt que de le signaler en note.
La correction ne l'a pas fait tomber : **l'argument passe par
l'attribution, non par la nature de CRITIQUE**, et il est ici plus
fort qu'avant puisqu'il s'appuie sur la machine du set et non sur la
mienne. -/

/-- NT-ARCH §4 — le niveau CRITIQUE n'est atteignable que depuis
    ATTRIBUEE. Démontré sur `transition_valide`, non sur une machine
    reconstruite. -/
theorem critique_exige_attribution (st : StatutDette)
    (h : transition_valide st NiveauRIA.critique) :
    st = StatutDette.attribuee := by
  cases st with
  | attribuee => rfl
  | nonAttribuee => exact absurd h (by simp [transition_valide])
  | enDeliberation => exact absurd h (by simp [transition_valide])

/-- **Un seuil NONDECLARE interdit d'entrer en ATTRIBUEE** — dans
    tout régime d'échéance. -/
theorem seuil_non_declare_interdit_attribution
    (e : Echeance) (d : Dette) (h : ACT_ARCH_001 e d)
    (h_nd : d.seuil = SeuilCommunauteMorale.nonDeclare) :
    d.statut ≠ StatutDette.attribuee := by
  intro h_att
  exact (h h_att).1 h_nd

/-- **L'enchaînement, démontré sur la machine du set.** Un seuil non
    déclaré interdit l'attribution ; le niveau CRITIQUE n'est
    atteignable que depuis l'attribution (§4) ; donc un seuil non
    déclaré rend le niveau CRITIQUE inatteignable.

    Conséquence politique, à lire et non à contourner : **qui a
    intérêt à ce que le seuil reste disputé n'a rien d'autre à faire
    que de le disputer.** La contestation du seuil devient une
    protection contre l'attribution — et le repli à échéance est ce
    qui la désamorce, puisqu'il permet d'attribuer pendant que le
    seuil se discute (§5). -/
theorem seuil_non_declare_bloque_critique
    (e : Echeance) (d : Dette) (h : ACT_ARCH_001 e d)
    (h_nd : d.seuil = SeuilCommunauteMorale.nonDeclare) :
    ¬ transition_valide d.statut NiveauRIA.critique := by
  intro htr
  exact seuil_non_declare_interdit_attribution e d h h_nd
    (critique_exige_attribution d.statut htr)

/-! ## 7. Composition avec PR-10

Le §A.14.7 type `seuilentreecommunautemorale` comme
**seuil-valuatif** — ligne « Architecture §5.1 », au motif que
« l'appliquer décide de la considérabilité : valuation non
décollable ». PR-10 s'applique donc à lui.

Le théorème qui suit compose deux règles actées séparément et
produit une exigence plus forte que celle qu'énonce §7bis. -/

open ProfRegPR10 in
/-- **Attribuer exige le seuil déclaré (PR-3) ET son quadruplet
    (PR-10).** Le premier conjoint vient de NT-ARCH §7bis, le second
    de la règle R0-bis via le typage §A.14.7. Ni l'un ni l'autre ne
    l'énonce : c'est leur composition qui le produit. -/
theorem attribution_exige_seuil_et_quadruplet
    (e : Echeance) (d : Dette) (m : Mobilisation)
    (h_act : ACT_ARCH_001 e d)
    (h_att : d.statut = StatutDette.attribuee)
    (h_type : m.primitive.charge = ChargeValuative.seuilValuatif)
    (h_bf : BienFormee m) :
    SeuilDeclare d ∧ ∃ s, m.statut = some s := by
  refine ⟨(h_act h_att).1, ?_⟩
  exact seuil_valuatif_must_declare_status m h_bf h_type

/-! ## 8. Ce que PR-3 ne fait pas -/

/-- **PR-3 ne dit pas quel seuil est le bon.** Il exige qu'un seuil
    soit déclaré ; il ne départage ni SENTIENCE ni
    FINALITEIMMANENTE, et n'en recommande aucun. Les deux régimes
    sont également conformes.

    C'est la limite délibérée de la règle : elle est **procédurale**,
    et le débat Nussbaum / Jonas qu'elle laisse ouvert n'est pas de
    son ressort. -/
theorem PR3_ne_departage_pas_les_seuils :
    (∃ d : Dette, ACT_ARCH_001 Echeance.aLAttribution d
                ∧ d.seuil = SeuilCommunauteMorale.sentience) ∧
    (∃ d : Dette, ACT_ARCH_001 Echeance.aLAttribution d
                ∧ d.seuil = SeuilCommunauteMorale.finaliteImmanente) := by
  constructor
  · refine ⟨{ statut := StatutDette.attribuee
            , seuil := SeuilCommunauteMorale.sentience
            , tAttribution := 3
            , tDeclarationSeuil := some 3 }, ?_, rfl⟩
    intro _
    refine ⟨?_, 3, rfl, Nat.le_refl 3⟩
    intro h; exact SeuilCommunauteMorale.noConfusion h
  · refine ⟨{ statut := StatutDette.attribuee
            , seuil := SeuilCommunauteMorale.finaliteImmanente
            , tAttribution := 3
            , tDeclarationSeuil := some 3 }, ?_, rfl⟩
    intro _
    refine ⟨?_, 3, rfl, Nat.le_refl 3⟩
    intro h; exact SeuilCommunauteMorale.noConfusion h

/-- **PR-3 ne choisit pas le régime.** Il existe des dettes conformes
    sous le repli qui ne le sont pas sous le régime strict : le
    théorème ne tranche donc pas la question que §7bis a laissée
    ouverte, il l'instrumente. Le choix reste au porteur, et il
    reste conditionné au constat empirique de récurrence que §7bis
    exige — non préempté ici. -/
theorem PR3_ne_choisit_pas_le_regime :
    ∃ (T : Nat) (d : Dette),
      ACT_ARCH_001 (Echeance.aDate T) d ∧ ¬ ACT_ARCH_001 Echeance.aLAttribution d := by
  obtain ⟨T, d, h1, _, h3⟩ := repli_autorise_l_attribution_avant_declaration
  exact ⟨T, d, h1, h3⟩

/-! ## Témoins D-13 (règle NT-ARCH §8ter-bis, R-2) — versés le 28/09/2026

Les dépliages d'`ACT_ARCH_001` sont des lectures (R-3). Clause « temps » :
témoins `PR3_ne_departage_pas_les_seuils` (bien formé) et
`PR3_ne_choisit_pas_le_regime` (mal formé, discriminant). Clause « seuil »
(`attribuee_seuil_declare_required`, `attribution_exige_un_seuil_declare`,
`seuil_non_declare_interdit_attribution`, et le premier conjoint de
`attribution_exige_seuil_et_quadruplet`) : témoin ci-dessous. -/

/-- Témoin discriminant de la clause « seuil » : dette attribuée, déclarée
    dans les temps, mais sans seuil. -/
theorem PR3_clauseSeuil_temoin_mal_forme :
    ∃ d : Dette, d.statut = .attribuee
      ∧ DeclareDansLesTemps d .aLAttribution
      ∧ ¬ ACT_ARCH_001 .aLAttribution d :=
  ⟨{ statut := .attribuee, seuil := .nonDeclare, tAttribution := 0,
     tDeclarationSeuil := some 0 },
   rfl, ⟨0, rfl, Nat.le_refl 0⟩, fun h => (h rfl).1 rfl⟩

end ProfRegPR3
