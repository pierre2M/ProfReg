import ProfReg.Actors
import Mathlib.Data.Finset.Basic

-- ============================================================
-- P₀ : régime ACTORIEL  -  profunctor booléen
-- P₀(a, b) = true ssi l'interaction a→b est inscrite
-- ============================================================

def P0 := Actor → Actor → Bool

-- Condition R1 sur P₀ : toute écriture a une écriture miroir
def R1_actoriel (p : P0) : Prop :=
  ∀ a b : Actor, p a b = true → p b a = true

-- Exemple minimal : interaction A→B sans miroir (viole R1)
def exemple_sans_miroir : P0 :=
  fun a b => (a == "did:mrc:acteur-A") && (b == "did:mrc:acteur-B")

-- Vérifier que R1 est violé sur cet exemple
theorem exemple_sans_miroir_viole_R1 : ¬ R1_actoriel exemple_sans_miroir := by
  intro h
  have h' := h "did:mrc:acteur-A" "did:mrc:acteur-B" (by simp [exemple_sans_miroir])
  simp [exemple_sans_miroir] at h'
  have hne : "did:mrc:acteur-A" ≠ "did:mrc:acteur-B" := by decide
  exact hne h'.2

-- ============================================================
-- P₁ : régime HYBRIDE  -  profunctor flou
-- Une interaction hybride déclare plusieurs débiteurs avec fractions
-- ============================================================

structure HybridInteraction where
  debtors  : Finset Actor
  creditor : Actor
  -- fraction pour chaque acteur (simplification : Actor → ℝ)
  fraction : Actor → ℝ
  -- les fractions sont dans [0,1]
  frac_pos  : ∀ a ∈ debtors, 0 ≤ fraction a
  frac_le1  : ∀ a ∈ debtors, fraction a ≤ 1
  -- elles somment à 1
  frac_sum  : debtors.sum fraction = 1
  -- le créancier n'est pas débiteur (évite l'autoréférence)
  no_self   : creditor ∉ debtors

-- Condition R1 sur P₁ : le miroir existe avec les mêmes fractions
-- (le créancier devient débiteur unique à fraction 1,
--  chaque ancien débiteur devient créancier proportionnel)
-- NOTE : cette définition du "miroir" est une DÉCISION ARCHITECTURALE
-- à valider par délibération  -  pas un calcul universel (cf. Callon 2025)
def R1_hybride (h : HybridInteraction) : Prop :=
  ∃ h_miroir : HybridInteraction,
    -- l'ancien créancier est le seul débiteur du miroir
    h_miroir.debtors = {h.creditor} ∧
    -- les anciens débiteurs deviennent créanciers (un seul à la fois)
    -- SIMPLIFICATION : on vérifie l'existence d'une inscription miroir
    -- pour chaque débiteur proportionnel
    ∀ a ∈ h.debtors, h_miroir.fraction h.creditor = 1

-- ============================================================
-- P₂ : régime SYSTEMIQUE  -  créancier potentiellement absent
-- ============================================================

structure SystemicInteraction where
  collectif : Finset Actor    -- collectif sans porteur unique
  creditor  : Option Actor    -- peut être None
  amount    : ENNReal         -- dette en ℝ≥0∞

-- Condition R1 sur P₂ : RÉSULTAT FORMEL
-- R1 standard est insatisfaisable si creditor = none
def R1_systemique (d : SystemicInteraction) : Prop :=
  match d.creditor with
  | some _ => True   -- créancier identifié : R1 satisfaisable
  | none   => False  -- créancier absent : R1 STANDARD non satisfait

-- Ce théorème formalise la tension T3 de la note d'amendements :
-- tout SystemicInteraction sans créancier viole R1
-- [C-13 — 28/09/2026] Lecture de `R1_systemique`, déclarée. `R1_systemique` est un
-- **indicateur de satisfaisabilité** (« un créancier est identifié »), non R1 :
-- il vaut `True` dès qu'un créancier existe, sans rien contrôler de plus. Le tri
-- est témoigné par `R1_systemique_ssi_creancier` ci-dessous.
theorem systemique_sans_creancier_viole_R1
    (d : SystemicInteraction) (h : d.creditor = none) :
    ¬ R1_systemique d := by
  simp [R1_systemique, h]

/-- Caractérisation de l'indicateur (C-13, 28/09/2026 ; patron
    `V1_commute_ssi_coherence`) : `R1_systemique` tient **exactement** quand un
    créancier est identifié. Témoigne que la définition trie, et borne ce qu'elle
    dit : rien au-delà de l'existence du créancier. -/
theorem R1_systemique_ssi_creancier (d : SystemicInteraction) :
    R1_systemique d ↔ d.creditor.isSome = true :=
  match d with
  | ⟨_, some _, _⟩ => ⟨fun _ => rfl, fun _ => trivial⟩
  | ⟨_, none, _⟩ => ⟨fun h => False.elim h, fun h => Bool.noConfusion h⟩
