# A Normalizing Computation Rule for Propositional Extensionality in Higher-Order Minimal Logic

This is an Agda formalization of the results in the paper A Normalizing Computation Rule for Propositional Extensionality in Higher-Order Minimal Logic,
submitted to the Post-Proceedings of the TYPES 2016 conference.

*Note* This formalization was built using Agda version 2.5.2 and the Agda standard library version 0.13.  It has not been tested with other versions of Agda.

The following is a guide to which lemmas in the paper correspond to which terms in the Agda formalisation


| Lemma | File | Term |
|---|---|---|
| Lemma 3.1 | PHOML / PathSub / PS.agda | pathSub-•PS |
| Lemma 3.2 | PHOML / PathSub / SP.agda | pathSub-•SP |
| Lemma 7 (Confluence) | PHOML / Red / Diamond.agda | diamond |
| Lemma 8 (Reduction respects path substitution) | PHOML / Red / Base.agda | ⇒-resp-ps |
| Lemma 10 (Context Validity) | PHOML / Meta / ConVal.agda | context-validity |
| Lemma 11 (Weakening) | PHOML / Meta / ConVal.agda | weakening |
| Lemma 12.1 (Type Validity) | PHOML / Meta / TypeVal.agda | prop-validity |
| Lemma 12.2 (Type Validity) | PHOML / Meta / TypeVal.agda | eq-validity₁ |
| | | eq-validity₂ |
| Lemma 13.1 (Generation) | PHOML / Meta / Gen / Term.agda | generation-var |
| Lemma 13.2 (Generation) | PHOML / Meta / Gen / Term.agda | generation-⊥ |
| Lemma 13.3 (Generation) | PHOML / Meta / Gen / Term.agda | generation-⊃₁ |
| | | generation-⊃₂ |
| | | generation-⊃₃ |
| Lemma 13.4 (Generation) | PHOML / Meta / Gen / Term.agda | generation-ΛT |
| Lemma 13.5 (Generation) | PHOML / Meta / Gen / Term.agda | generation-appT |
| Lemma 13.6 (Generation) | PHOML / Meta / Gen / Proof.agda | generation-varP |
| Lemma 13.7 (Generation) | PHOML / Meta / Gen / Proof.agda | generation-ΛP |
| Lemma 13.8 (Generation) | PHOML / Meta / Gen / Proof.agda | generation-appP |
| Lemma 13.9 (Generation) | PHOML / Meta / Gen / Path.agda | generation-varE |
| Lemma 13.10 (Generation) | PHOML / Meta / Gen / Path.agda | generation-reff₁ |
| | | generation-reff₂ |
| | | generation-reff₃ |
| Lemma 13.11 (Generation) | PHOML / Meta / Gen / Path.agda | generation-⊃* |
| Lemma 13.12 (Generation) | PHOML / Meta / Gen / Path.agda | generation-univ₁ |
| | | generation-univ₂ |
| | | generation-univ₃ |
| | | generation-univ₄ |
| Lemma 13.13 (Generation) | PHOML / Meta / Gen / Path.agda | generation-λλλ |
| Lemma 13.14 (Generation) | PHOML / Meta / Gen / Path.agda | generation-app* |
| Lemma 13.15 (Generation) | PHOML / Meta / Gen / Proof.agda | generation-plus |
| Lemma 13.16 (Generation) | PHOML / Meta / Gen / Proof.agda | generation-minus |
| Lemma 15 (Well-Typed Substitution) | PHOML / Meta / Sub.agda | substitution |
| Lemma 17 (Path Substitution) | PHOML / Meta / PathSub.agda | path-substitution |
| Proposition 18 (Subject Reduction) | PHOML / Meta / SubRed.agda | subject-reduction |
| Lemma 20 | PHOML / Canon / Prp.agda | red-canon |
| Lemma 24 (Conversion) | PHOML / Compute / Prp.agda | conversionP |
| | PHOML / Compute / TermPath.agda | conversionE |
| Lemma 25 (Expansion) | PHOML / Compute / TermPath.agda | expansionT |
| | PHOML / Compute / Prp.agda | expansionP |
| | PHOML / Compute / TermPath.agda | expansionE |
| Lemma 26 (Reduction) | PHOML / Compute / TermPath.agda | reductionT |
| | PHOML / Compute / Prp.agda | reductionP |
| | PHOML / Compute / TermPath.agda | reductionE |
| Lemma 28 | PHOML / Compute / TermPath.agda | ⊧c |
| Lemma 29.1 (Weak Normalization) | PHOML / Compute / Prp.agda | ⊧P-wn |
| Lemma 29.2 (Weak Normalization) | PHOML / Compute / TermPath.agda | ⊧E-wn |
| Lemma 29.3 (Weak Normalization) | PHOML / Compute / TermPath.agda | ⊧canon |
| | | ⊧T-rtΛ |
| Lemma 30 | PHOML / Compute / TermPath.agda | ⊧T-rtΛ |
| Lemma 31 | PHOML / Compute / TermPath.agda | ⊧refP |
| Lemma 32 | PHOML / Compute / TermPath.agda | ⊧canon |
| | | ⊧canon' |
| Lemma 33 | PHOML / Compute / Prp.agda | ⊧neutralP |
| Lemma 34 | PHOML / Compute / TermPath.agda | ⊧neutralE |
| Lemma 35 | PHOML / Compute / TermPath.agda | ⊧ref |
| Lemma 36 | PHOML / Lemma35.agda | ⊧⊃* |
| Lemma 37 | PHOML / Compute / TermPath.agda | ⊧univ |
| Theorem 38.1 | PHOML / MainTheorem.agda | soundness |
| Theorem 38.2 | PHOML / MainTheorem.agda | soundness-path |
| Corollary 39.1 | PHOML / Corollaries.agda | canonicityP |
| Corollary 39.2 | PHOML / Corollaries.agda | canonicityE |
| Corollary 41 (Consistency) | PHOML / Corollaries.agda | consistency |