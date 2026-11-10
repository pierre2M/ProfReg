/-
  ProfReg — PR-27 [VERSÉ AU PROGRAMME LE 28/09/2026 — décision de porteur D-12] — Candidats issus des
  modifications du set entre le 9 et le 26 septembre 2026. Audit du 26 septembre 2026.

  Quatre lots, chacun de la classe ProfReg (non-implication ou bonne formation) :
    §1 AX-3 — [depuis D-10, 28/09] la qualification de PR-12 coïncide avec celle
           de la fiche versée au set (§A.18.2, quatre conditions) ;
    §2 AX-3 — répartiteur ≠ décideur (NT-ARCH §4.2ter, 15 sept.) : une avarie qualifiée
           ne rend pas une répartition bien formée ;
    §3 CONV-4 bornée (19 sept.) — `fraction_exhibe_sa_source` admet une source vide :
           l'obligation compilée est plus faible que la convention ;
    §4 CONV-14 (11 sept.) — un score de communalité agrégé ne détermine pas les axes.

  Importé par `ProfReg.lean` depuis le 28/09 (D-12). Rien ici n'établit une thèse du MRC.
-/
import ProfReg.PR12_NonConfusionDettes
import ProfReg.LotL2_PR2_PR14

namespace ProfRegPR27

open ProfRegPR12

/-! ## §1. AX-3 : cinq conditions dans PR-12, quatre dans la fiche du set -/

/-- Les quatre conditions de §A.18.2 (droit maritime, « reprises telles quelles »). -/
def qualifieeSelonLaFiche (c : ConditionsAvarie) : Bool :=
  c.perilCommun && c.sacrificeVolontaire && c.interetCommun && c.resultatUtile

/-- **Depuis D-10 (28/09/2026), PR-12 coïncide avec la fiche** : la qualification
    compilée est exactement celle de §A.18.2. (Avant D-10, PR-12 exigeait une
    cinquième condition ; l'écart est soldé en la déplaçant sur le mandat, AX-9.)

    `[GARDE DE NON-RÉGRESSION — VRAIE PAR CONSTRUCTION, DÉCLARÉE]` L'énoncé se prouve
    par `rfl` : il n'établit rien du monde. Son rôle est d'**échouer à compiler** si
    PR-12 et la fiche divergeaient de nouveau (règle D-13, à arrêter). -/
theorem PR12_coincide_avec_la_fiche (c : ConditionsAvarie) :
    avarieQualifiee c = qualifieeSelonLaFiche c := rfl

/-! ## §2. AX-3 : le répartiteur n'est pas le décideur -/

/-- Une répartition inscrite : qui a décidé le sacrifice, qui répartit. -/
structure Repartition where
  conditions          : ConditionsAvarie
  porteurDecision     : Option Nat   -- DID, abrégé en identifiant
  porteurRepartition  : Option Nat
  deriving Repr

/-- Bonne formation (NT-ARCH §4.2ter) : les deux porteurs sont nommés et distincts. -/
def RepartitionBienFormee (r : Repartition) : Bool :=
  match r.porteurDecision, r.porteurRepartition with
  | some d, some p => d != p
  | _, _           => false

/-- **Non-implication.** Une avarie qualifiée — même au sens le plus strict, celui de
    PR-12 — ne rend pas la répartition bien formée : si le décideur répartit, le
    découplage que AX-3 pose est défait. -/
theorem l_avarie_qualifiee_ne_suffit_pas :
    ∃ r : Repartition,
      avarieQualifiee r.conditions = true ∧ RepartitionBienFormee r = false :=
  ⟨⟨⟨true, true, true, true⟩, some 7, some 7⟩, rfl, rfl⟩

/-- **Et le répartiteur non nommé n'est pas un répartiteur distinct** : le silence
    ne vaut pas découplage (patron PR-17). -/
theorem le_repartiteur_non_nomme_ne_decouple_pas (c : ConditionsAvarie) (d : Option Nat) :
    RepartitionBienFormee ⟨c, d, none⟩ = false := by
  cases d <;> rfl

/-! ## §3. CONV-4 bornée : l'obligation compilée admet la source vide -/

open ProfRegLot in
/-- **`fraction_exhibe_sa_source` n'établit pas une source déclarée et vérifiable.**
    Le type admet un habitant à source vide ; le théorème s'y applique. Ce que le set
    écrit — « l'obligation de source est portée par CONV-4 / `fraction_exhibe_sa_source` »
    — surévalue le compilé (forme 8 appliquée à ce que le set dit de ProfReg). -/
theorem fraction_exhibe_une_source_eventuellement_vide :
    ∃ f : FractionActorielle, ∃ v, f = FractionActorielle.declaree "" v :=
  ⟨FractionActorielle.declaree "" "0,4", "0,4", rfl⟩

/-! ## §4. CONV-14 : l'échelle de communalité ne s'agrège pas -/

/-- Un profil de communalité sur trois axes (valeurs ordinales). -/
structure Profil where
  axe1 : Nat
  axe2 : Nat
  axe3 : Nat
  deriving DecidableEq, Repr

/-- Un score agrégé — la somme, le plus simple et le plus courant. -/
def score (p : Profil) : Nat := p.axe1 + p.axe2 + p.axe3

/-- **Non-implication (CONV-14).** Deux profils distincts ont le même score : le score
    ne permet pas de retrouver les axes. Le témoin est choisi pour que les deux
    profils diffèrent sur **chaque** axe. -/
theorem le_score_ne_determine_pas_les_axes :
    ∃ p q : Profil, p ≠ q ∧ p.axe1 ≠ q.axe1 ∧ p.axe2 ≠ q.axe2 ∧ p.axe3 ≠ q.axe3
      ∧ score p = score q :=
  ⟨⟨3, 0, 1⟩, ⟨0, 2, 2⟩, by decide, by decide, by decide, by decide, rfl⟩

/-! ## Témoins D-13 (règle NT-ARCH §8ter-bis, R-2) — versés le 28/09/2026

`le_repartiteur_non_nomme_ne_decouple_pas` est une lecture de
`RepartitionBienFormee` (R-3). Témoin mal formé : `l_avarie_qualifiee_ne_suffit_pas`. -/

/-- Témoin bien formé de `RepartitionBienFormee` : deux porteurs nommés distincts. -/
theorem PR27_temoin_bien_forme :
    ∃ r : Repartition, RepartitionBienFormee r = true :=
  ⟨⟨⟨true, true, true, true⟩, some 1, some 2⟩, rfl⟩

end ProfRegPR27
