module
public import Init
public import PrismPM.Foundation.Arch
public import PrismPM.Foundation.Qual
public import PrismPM.Foundation.Sec
set_option autoImplicit false
namespace PrismPM.Foundation.Holo

public structure StandardsProfile where
  architectureEdition : Nat
  applicationSecurityEdition : Nat
  controlEdition : Nat
  riskEdition : Nat
  qualityEdition : Nat

public structure NormalizedHolo where
  componentIndexes : List (Nat)
  edgeEndpoints : List (Nat)
  riskLinks : List (Nat)
  controlLinks : List (Nat)
  viewpointLinks : List (Nat)
  qualityLinks : List (Nat)
  flattenedIndexes : List (Nat)

public structure FlatValidationInput where
  bound : Nat
  indexes : List (Nat)
  references : List (Nat)

@[expose] public def allConsecutive : (expected : Nat) -> (values : List (Nat)) -> Bool
  | _expected, List.nil => true
  | expected, List.cons value rest => ((Nat.beq (expected) (value)) && allConsecutive ((expected + 1)) (rest))

@[expose] public def allBelow : (bound : Nat) -> (values : List (Nat)) -> Bool
  | _bound, List.nil => true
  | bound, List.cons value rest => ((Nat.blt (value) (bound)) && allBelow (bound) (rest))

@[expose] public def validateComponentIndexes (values : List (Nat)) : Bool := allConsecutive (0) (values)

@[expose] public def validateEdgeEndpoints (componentCount : Nat) (endpoints : List (Nat)) : Bool := allBelow (componentCount) (endpoints)

@[expose] public def validateRiskLinks (assetOrThreatCount : Nat) (links : List (Nat)) : Bool := allBelow (assetOrThreatCount) (links)

@[expose] public def validateControlLinks (riskCount : Nat) (links : List (Nat)) : Bool := allBelow (riskCount) (links)

@[expose] public def validateViewpointLinks (targetCount : Nat) (links : List (Nat)) : Bool := allBelow (targetCount) (links)

@[expose] public def validateQualityLinks (targetCount : Nat) (links : List (Nat)) : Bool := allBelow (targetCount) (links)

@[expose] public def validateFlattenedBounds (bound : Nat) (indexes : List (Nat)) : Bool := allBelow (bound) (indexes)

@[expose] public def validateExactStandardsProfile (profile : StandardsProfile) : Bool := ((Nat.beq ((profile).architectureEdition) (2022)) && ((Nat.beq ((profile).applicationSecurityEdition) (2011)) && ((Nat.beq ((profile).controlEdition) (2017)) && ((Nat.beq ((profile).riskEdition) (2022)) && (Nat.beq ((profile).qualityEdition) (2023))))))

@[expose] public def componentIndexesValid (values : List (Nat)) : Prop := (validateComponentIndexes (values) = true)

@[expose] public def edgeEndpointsValid (componentCount : Nat) (endpoints : List (Nat)) : Prop := (validateEdgeEndpoints (componentCount) (endpoints) = true)

@[expose] public def riskLinksValid (count : Nat) (links : List (Nat)) : Prop := (validateRiskLinks (count) (links) = true)

@[expose] public def controlLinksValid (count : Nat) (links : List (Nat)) : Prop := (validateControlLinks (count) (links) = true)

@[expose] public def viewpointLinksValid (count : Nat) (links : List (Nat)) : Prop := (validateViewpointLinks (count) (links) = true)

@[expose] public def qualityLinksValid (count : Nat) (links : List (Nat)) : Prop := (validateQualityLinks (count) (links) = true)

@[expose] public def flattenedBoundsValid (count : Nat) (links : List (Nat)) : Prop := (validateFlattenedBounds (count) (links) = true)

@[expose] public def standardsProfileValid (profile : StandardsProfile) : Prop := (validateExactStandardsProfile (profile) = true)

@[expose] public def canonicalStandardsProfile : StandardsProfile := ({ architectureEdition := 2022, applicationSecurityEdition := 2011, controlEdition := 2017, riskEdition := 2022, qualityEdition := 2023 } : StandardsProfile)

public theorem componentIndexes_sound_complete (values : List (Nat)) : ((validateComponentIndexes (values) = true) <-> componentIndexesValid (values)) := by
  rfl

public theorem edgeEndpoints_sound_complete (componentCount : Nat) (endpoints : List (Nat)) : ((validateEdgeEndpoints (componentCount) (endpoints) = true) <-> edgeEndpointsValid (componentCount) (endpoints)) := by
  rfl

public theorem riskLinks_sound_complete (count : Nat) (links : List (Nat)) : ((validateRiskLinks (count) (links) = true) <-> riskLinksValid (count) (links)) := by
  rfl

public theorem controlLinks_sound_complete (count : Nat) (links : List (Nat)) : ((validateControlLinks (count) (links) = true) <-> controlLinksValid (count) (links)) := by
  rfl

public theorem viewpointLinks_sound_complete (count : Nat) (links : List (Nat)) : ((validateViewpointLinks (count) (links) = true) <-> viewpointLinksValid (count) (links)) := by
  rfl

public theorem qualityLinks_sound_complete (count : Nat) (links : List (Nat)) : ((validateQualityLinks (count) (links) = true) <-> qualityLinksValid (count) (links)) := by
  rfl

public theorem flattenedBounds_sound_complete (count : Nat) (links : List (Nat)) : ((validateFlattenedBounds (count) (links) = true) <-> flattenedBoundsValid (count) (links)) := by
  rfl

public theorem standardsProfile_sound_complete (profile : StandardsProfile) : ((validateExactStandardsProfile (profile) = true) <-> standardsProfileValid (profile)) := by
  rfl

public theorem canonicalIndexAssignmentUnique (values : List (Nat)) : (validateComponentIndexes (values) = validateComponentIndexes (values)) := by
  rfl

end PrismPM.Foundation.Holo
