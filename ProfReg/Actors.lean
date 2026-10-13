import ProfReg.BaseCategories

-- Un acteur MRC est identifié par son DID (simplifié en String)
def Actor : Type := String
deriving DecidableEq, Repr

-- Exemples d'acteurs pour les tests
def actorA : Actor := "did:mrc:acteur-A"
def actorB : Actor := "did:mrc:acteur-B"
def actorC : Actor := "did:mrc:acteur-C"
