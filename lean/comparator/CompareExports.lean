import Main

/-! Local development check against the pinned upstream Comparator API.
Input exports are produced by the pinned lean4export. No OS sandbox is claimed.
Setting PUBLICATION_REPLAY=1 runs only the upstream built-in kernel replay. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#eval show IO Unit from do
  let some dir ← IO.getEnv "PUBLICATION_EXPORT_DIR"
    | throw <| IO.userError "PUBLICATION_EXPORT_DIR is required"
  let cfg : Comparator.Config := {
    challenge_module := "Challenge"
    solution_module := "FCSolution"
    theorem_names := #[
      "ReversibleFinslerSphereFC.infinitely_many_prime_closed_geodesics",
      "ReversibleFinslerSphereFC.variational_form"]
    permitted_axioms := #["propext", "Classical.choice", "Quot.sound"]
    enable_nanoda? := some false
    external_kernels? := none
  }
  Comparator.M.run (do
    let solutionFile ← IO.FS.Handle.mk (System.FilePath.mk dir / "FCSolution.export") .read
    let solution ← Export.parseStream (IO.FS.Stream.ofHandle solutionFile)
    if (← IO.getEnv "PUBLICATION_REPLAY") == some "1" then
      let result ← Comparator.runBuiltinKernel solution
      if let some error := result then throw <| IO.userError error
      IO.println "PASS: upstream Comparator built-in kernel replay"
    else
      let challengeFile ← IO.FS.Handle.mk (System.FilePath.mk dir / "Challenge.export") .read
      let challenge ← Export.parseStream (IO.FS.Stream.ofHandle challengeFile)
      let names ← Comparator.getTheoremNames
      let axioms ← Comparator.getLegalAxioms
      IO.ofExcept <| Comparator.compareAt challenge solution (names ++ axioms) #[]
        (← Comparator.primitiveTargets)
      IO.ofExcept <| Comparator.checkAxioms solution names #[] axioms
      IO.println "PASS: upstream Comparator.compareAt and Comparator.checkAxioms"
  ) cfg

