import Formalize.PaperBridge

open Formalize.PaperBridge

example : ArtifactType := ArtifactType.minedDecl

example : Type := Schema

example : ArtifactState := initialState

example : Provenance initialState := sampleMinedArtifact

example : Provenance initialState := sampleCheckedArtifact

example : Provenance initialState := sampleProofArtifact

example : ProofOutcome := ProofOutcome.pending

example : initialState.obj ArtifactType.minedDecl := sampleMinedDecl

example :
    initialState.map (Quiver.Hom.toPath ArtifactOp.checkWellFormed) sampleMinedDecl =
      { source := sampleMinedDecl.name, statement := sampleMinedDecl.statement } :=
  rfl
