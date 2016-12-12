# A Normalizing Computation Rule for Propositional Extensionality in Higher-Order Minimal Logic

This is an Agda formalization of the results in the paper A Normalizing Computation Rule for Propositional Extensionality in Higher-Order Minimal Logic,
submitted to the Post-Proceedings of the TYPES 2016 conference.

The following is a guide to which lemmas in the paper correspond to which terms in the Agda formalisation


| Lemma | File | Term |
|---|---|---|
| Lemma 3.1 | PHOML / PathSub.agda | pathsub-•PS |
| Lemma 3.2 | PHOML / PathSub.agda | pathSub-•SP |
| Lemma 7 (Diamond Property) | PHOML / Red / Diamond.agda | diamond |
| Lemma 8 (Reduction respects path substitution) | PHOML / Red / Base.agda | ⇒-resp-ps |
| Lemma 10 | PHOML / Canon.agda | red-canon |
| Lemma 13 (Context Validity) | PHOML / Meta / ConVal.agda | context-validity |
| Lemma 14 (Weakening) | PHOML / Meta / ConVal.agda | weakening |
| Lemma 15.1 (Type Validity) | PHOML / Meta.agda | Prop-Validity |
| Lemma 15.2 (Type Validity) | PHOML / Meta.agda | eq-validity₁ |
| Lemma 17 (Subject Reduction) | PHOML / Meta.agda | Subject-Reduction-R |
| Lemma 19 (Well-Typed Substitution) | PHOML / Meta.agda | substitution |
| Lemma 24 (Conversion) | PHOML / Compute.agda | conversionP, conversionE |
| Lemma 25 (Expansion) | PHOML / Compute.agda | expansionT, expansionP, expansionE |
| Lemma 26 (Reduction) | PHOML / Compute.agda | reductionT, reductionP, reductionE |
| Lemma 28 | PHOML / Compute.agda | ⊧c |
| Lemma 30 | PHOML / Compute.agda | Lemma30 |
| Lemma 31 | PHOML / Compute.agda | ⊧ref |
| Lemma 32 | PHOML / Compute.agda | ⊧canon, ⊧canon' |