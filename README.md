# TYPES2016

This is an Agda formalization of the results in the paper A Normalizing Computation Rule for Propositional Extensionality in Higher-Order Minimal Logic,
submitted to the Post-Proceedings of the TYPES 2016 conference.

The following is a guide to which lemmas in the paper correspond to which terms in the Agda formalisation


| Lemma | File | Term |
|---|---|---|
| Lemma 3.1 | PHOPL / PathSub.agda | pathsub-•PS |
| Lemma 3.2 | PHOPL / PathSub.agda | pathSub-•SP |
| Lemma 7 (Diamond Property) | PHOPL / Red / Diamond.agda | diamond |
| Lemma 8 (Reduction respects path substitution) | PHOPL / Red / Base.agda | ⇒-resp-ps |
| Lemma 10 | PHOPL / Canon.agda | red-canon |
| Lemma 13 (Context Validity) | PHOPL / Meta / ConVal.agda | context-validity |
| Lemma 14 (Weakening) | PHOPL / Meta / ConVal.agda | weakening |
| Lemma 15.1 (Type Validity) | PHOPL / Meta.agda | Prop-Validity |
| Lemma 15.2 (Type Validity) | PHOPL / Meta.agda | eq-validity₁ |
| Lemma 17 (Subject Reduction) | PHOPL / Meta.agda | Subject-Reduction-R |
| Lemma 19 (Well-Typed Substitution) | PHOPL / Meta.agda | substitution |
| Lemma 24 (Conversion) | PHOPL / Compute.agda | conversionP, conversionE |
| Lemma 25 (Expansion) | PHOPL / Compute.agda | expansionT, expansionP, expansionE |
| Lemma 26 (Reduction) | PHOPL / Compute.agda | reductionT, reductionP, reductionE |
| Lemma 28 | PHOPL / Compute.agda | ⊧c |
| Lemma 30 | PHOPL / Compute.agda | Lemma30 |
| Lemma 31 | PHOPL / Compute.agda | ⊧ref |
| Lemma 32 | PHOPL / Compute.agda | ⊧canon, ⊧canon' |