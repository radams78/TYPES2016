module PHOPL.Red.Meta where
open import Data.Empty renaming (⊥ to False)
open import Data.Unit
open import Data.Vec
open import Data.Product renaming (_,_ to _,p_)
open import Data.List
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.PathSub
open import PHOPL.Red.Base
open import Reduction PHOPL β as Redβ
open import Reduction PHOPL R₀ as Red₀
open import Reduction PHOPL R as Red
open import Reduction.Subred PHOPL

R₀-imp-R : ∀ {V C K} {E F : Subexp V C K} → E Red₀.⇒ F → E Red.⇒ F
R₀-imp-R = Subred.sub-osr R₀ R R₀R

↠₀-imp-↠ : ∀ {V C K} {E F : Subexp V C K} → E Red₀.↠ F → E Red.↠ F
↠₀-imp-↠ (inc E⇒F) = inc (R₀-imp-R E⇒F)
↠₀-imp-↠ ref = ref
↠₀-imp-↠ (trans E↠F F↠G) = RTClose.trans (↠₀-imp-↠ E↠F) (↠₀-imp-↠ F↠G)

R₀?-imp-R? : ∀ {V C K} {E F : Subexp V C K} → E Red₀.⇒? F → E Red.⇒? F
R₀?-imp-R? (inc E⇒F) = inc (R₀-imp-R E⇒F)
R₀?-imp-R? ref = ref

β-imp-R : ∀ {V C K} {E F : Subexp V C K} → E Redβ.⇒ F → E Red.⇒ F
β-imp-R (Redβ.redex cE▷F) = Red.redex (βR cE▷F)
β-imp-R (Redβ.app EE⇒FF) = Red.app (β-imp-R EE⇒FF)
β-imp-R (Redβ.appl E⇒F) = Red.appl (β-imp-R E⇒F)
β-imp-R (Redβ.appr EE⇒FF) = Red.appr (β-imp-R EE⇒FF)

R-det : ∀ {V} {K} {C} {c : Con (SK C K)} {E : ListAbs V C} {F} {G} → R c E F → R c E G → F ≡ G
R-det (βR βT) (R₀R ())
R-det (R₀R ()) (βR βT)
R-det (βR βT) (βR βT) = refl
R-det (R₀R (βR _ _)) (R₀R (βR _ _)) = refl
R-det (R₀R (dir-ref _)) (R₀R (dir-ref _)) = refl
R-det (R₀R (plus-univ _)) (R₀R (plus-univ _)) = refl
R-det (R₀R (minus-univ _)) (R₀R (minus-univ _)) = refl
R-det (R₀R (ref⊃*univ _ _)) (R₀R (ref⊃*univ _ _)) = refl
R-det (R₀R (univ⊃*ref _ _)) (R₀R (univ⊃*ref _ _)) = refl
R-det (R₀R (univ⊃*univ _ _)) (R₀R (univ⊃*univ _ _)) = refl
R-det (R₀R (ref⊃*ref _ _)) (R₀R (ref⊃*ref _ _)) = refl
R-det (R₀R (refref _ _)) (R₀R (refref _ _)) = refl
R-det (R₀R (refref _ _)) (R₀R (reflam _ _ _ _ ()))
R-det (R₀R (βE _ _ _ _)) (R₀R (βE _ _ _ _)) = refl
R-det (R₀R (reflam _ _ _ _ _)) (R₀R (reflam _ _ _ _ _)) = refl
R-det (R₀R (reflam _ _ _ _ ())) (R₀R (refref _ _))

postulate nf-is-nf : ∀ {V K} {E E' : Expression V K} → nf E → E Red.⇒ E' → False
{- nf-is-nf (nfvar _) ()
nf-is-nf nf⊥ (redex ())
nf-is-nf nf⊥ (app ())
nf-is-nf (nf⊃ _ _) (redex ())
nf-is-nf (nf⊃ nfφ _) (app (appl φ⇒φ')) = nf-is-nf nfφ φ⇒φ'
nf-is-nf (nf⊃ _ nfψ) (app (appr (appl ψ⇒ψ'))) = nf-is-nf nfψ ψ⇒ψ'
nf-is-nf (nf⊃ _ _) (app (appr (appr ())))
nf-is-nf (nfΛT _ _) (redex ())
nf-is-nf (nfΛT _ nfM) (app (appl M⇒M')) = nf-is-nf nfM M⇒M'
nf-is-nf (nfΛT _ _) (app (appr ()))
nf-is-nf (nfappTvar _ _) (redex ())
nf-is-nf (nfappTvar _ _) (app (appl ()))
nf-is-nf (nfappTvar _ nfM) (app (appr (appl M⇒M'))) = nf-is-nf nfM M⇒M'
nf-is-nf (nfappTvar _ _) (app (appr (appr ())))
nf-is-nf (nfappT⊥ _) (redex ())
nf-is-nf (nfappT⊥ _) (app (appl ⊥⇒E')) = nf-is-nf nf⊥ ⊥⇒E'
nf-is-nf (nfappT⊥ nfM) (app (appr (appl M⇒M'))) = nf-is-nf nfM M⇒M'
nf-is-nf (nfappT⊥ _) (app (appr (appr ())))
nf-is-nf (nfappT⊃ _ _ _) (redex ())
nf-is-nf (nfappT⊃ nfM nfM' _) (app (appl M⊃M'⇒E')) = nf-is-nf (nf⊃ nfM nfM') M⊃M'⇒E'
nf-is-nf (nfappT⊃ _ _ nfN) (app (appr (appl N⇒N'))) = nf-is-nf nfN N⇒N'
nf-is-nf (nfappT⊃ _ _ _) (app (appr (appr ())))
nf-is-nf (nfappTappT _ _) (redex ())
nf-is-nf (nfappTappT nfMM' _) (app (appl MM'⇒E')) = nf-is-nf nfMM' MM'⇒E'
nf-is-nf (nfappTappT _ nfN) (app (appr (appl N⇒N'))) = nf-is-nf nfN N⇒N'
nf-is-nf (nfappTappT nfE nfE₁) (app (appr (appr ())))
nf-is-nf (nfΛP _ _) (redex ())
nf-is-nf (nfΛP nfφ _) (app (appl φ⇒φ')) = nf-is-nf nfφ φ⇒φ'
nf-is-nf (nfΛP _ nfδ) (app (appr (appl δ⇒δ'))) = nf-is-nf nfδ δ⇒δ'
nf-is-nf (nfΛP _ _) (app (appr (appr ())))
nf-is-nf (nfappPvar _ _) (redex ())
nf-is-nf (nfappPvar _ _) (app (appl ()))
nf-is-nf (nfappPvar _ nfδ) (app (appr (appl δ⇒δ'))) = nf-is-nf nfδ δ⇒δ'
nf-is-nf (nfappPvar _ _) (app (appr (appr ())))
nf-is-nf (nfappPappP _ _) (redex ())
nf-is-nf (nfappPappP nfδε _) (app (appl δε⇒E')) = nf-is-nf nfδε δε⇒E'
nf-is-nf (nfappPappP _ nfε') (app (appr (appl ε'⇒E'))) = nf-is-nf nfε' ε'⇒E'
nf-is-nf (nfappPappP _ _) (app (appr (appr ())))
nf-is-nf (nfappPdir _ _) (redex ())
nf-is-nf (nfappPdir nfdP _) (app (appl dP⇒E')) = nf-is-nf nfdP dP⇒E'
nf-is-nf (nfappPdir _ nfδ) (app (appr (appl δ⇒δ'))) = nf-is-nf nfδ δ⇒δ'
nf-is-nf (nfappPdir _ _) (app (appr (appr ())))
nf-is-nf (nfdirvar (var _) _ (nruvar _)) (redex ())
nf-is-nf (nfdirvar _ _ nru⊃*) (redex ())
nf-is-nf (nfdirvar _ _ nruλλλ) (redex ())
nf-is-nf (nfdirvar _ _ nruapp*) (redex ())
nf-is-nf (nfdirvar _ nfP _) (app (appl P⇒P')) = nf-is-nf nfP P⇒P'
nf-is-nf (nfdirvar _ _ _) (app (appr ()))
nf-is-nf (nfreff _) (redex ())
nf-is-nf (nfreff nfM) (app (appl M⇒M')) = nf-is-nf nfM M⇒M'
nf-is-nf (nfreff _) (app (appr ()))
nf-is-nf (nf⊃*l _ _ (nruvar _)) (redex ()) 
nf-is-nf (nf⊃*l _ _ nru⊃*) (redex ()) 
nf-is-nf (nf⊃*l _ _ nruλλλ) (redex ()) 
nf-is-nf (nf⊃*l _ _ nruapp*) (redex ()) 
nf-is-nf (nf⊃*l nfP _ _) (app (appl P⇒P')) = nf-is-nf nfP P⇒P'
nf-is-nf (nf⊃*l _ nfQ _) (app (appr (appl Q⇒Q'))) = nf-is-nf nfQ Q⇒Q'
nf-is-nf (nf⊃*l _ _ _) (app (appr (appr ())))
nf-is-nf (nf⊃*r _ _ (nruvar _)) (redex ()) 
nf-is-nf (nf⊃*r _ _ nru⊃*) (redex ()) 
nf-is-nf (nf⊃*r _ _ nruλλλ) (redex ()) 
nf-is-nf (nf⊃*r _ _ nruapp*) (redex ()) 
nf-is-nf (nf⊃*r nfP _ _) (app (appl P⇒P')) = nf-is-nf nfP P⇒P'
nf-is-nf (nf⊃*r _ nfQ _) (app (appr (appl Q⇒Q'))) = nf-is-nf nfQ Q⇒Q'
nf-is-nf (nf⊃*r _ _ _) (app (appr (appr ())))
nf-is-nf (nfuniv _ _ _ _) (redex ())
nf-is-nf (nfuniv nfφ _ _ _) (app (appl φ⇒φ')) = nf-is-nf nfφ φ⇒φ'
nf-is-nf (nfuniv _ nfψ _ _) (app (appr (appl ψ⇒ψ'))) = nf-is-nf nfψ ψ⇒ψ'
nf-is-nf (nfuniv _ _ nfδ _) (app (appr (appr (appl δ⇒δ')))) = nf-is-nf nfδ δ⇒δ'
nf-is-nf (nfuniv _ _ _ nfε) (app (appr (appr (appr (appl ε⇒ε'))))) = nf-is-nf nfε ε⇒ε'
nf-is-nf (nfuniv _ _ _ _) (app (appr (appr (appr (appr ())))))
nf-is-nf (nfλλλ _) (redex ())
nf-is-nf (nfλλλ nfP) (app (appl P⇒P')) = nf-is-nf nfP P⇒P'
nf-is-nf (nfλλλ _) (app (appr ()))
nf-is-nf (nfapp* _ _ _ _ (nrλvar _)) (redex ())
nf-is-nf (nfapp* _ _ _ _ nrλ⊃*) (redex ())
nf-is-nf (nfapp* _ _ _ _ nrλuniv) (redex ())
nf-is-nf (nfapp* _ _ _ _ nrλapp*) (redex ())
nf-is-nf (nfapp* nfM _ _ _ _) (app (appl M⇒M')) = nf-is-nf nfM M⇒M'
nf-is-nf (nfapp* _ nfN _ _ _) (app (appr (appl N⇒N'))) = nf-is-nf nfN N⇒N'
nf-is-nf (nfapp* _ _ nfP _ _) (app (appr (appr (appl P⇒P')))) = nf-is-nf nfP P⇒P'
nf-is-nf (nfapp* _ _ _ nfQ _) (app (appr (appr (appr (appl Q⇒Q'))))) = nf-is-nf nfQ Q⇒Q'
nf-is-nf (nfapp* _ _ _ _ _) (app (appr (appr (appr (appr ()))))) -}

postulate nfredexproof : ∀ {V} {AA} {c : Con (SK AA (varKind -Proof))} {EE EE' : ListAbs V AA} {δ} → R₀ c EE δ → EE Red.⇒ EE' → False
{-nfredexproof (βR nfΛPφδ _) (appl ΛPφδ⇒E') = nf-is-nf nfΛPφδ ΛPφδ⇒E'
nfredexproof (βR _ nfε) (appr (appl ε⇒ε')) = nf-is-nf nfε ε⇒ε'
nfredexproof (βR _ _) (appr (appr ()))
nfredexproof (dir-ref nfrefφ) (appl refφ⇒E') = nf-is-nf nfrefφ refφ⇒E'
nfredexproof (dir-ref _) (appr ())
nfredexproof (plus-univ nfP) (appl P⇒P') = nf-is-nf nfP P⇒P'
nfredexproof (plus-univ _) (appr ())
nfredexproof (minus-univ nfP) (appl P⇒P') = nf-is-nf nfP P⇒P'
nfredexproof (minus-univ _) (appr ())-}

nfredexpath : ∀ {V} {AA} {c : Con (SK AA (varKind -Path))} {EE EE' : ListAbs V AA} {P} → R₀ c EE P → EE Red.⇒ EE' → False
nfredexpath (ref⊃*univ nfrefφ _) (Red.appl refφ⇒EE') = nf-is-nf nfrefφ refφ⇒EE'
nfredexpath (ref⊃*univ _ nfunivδε) (Red.appr (Red.appl univδε⇒EE')) = nf-is-nf nfunivδε univδε⇒EE'
nfredexpath (ref⊃*univ _ _) (Red.appr (Red.appr ()))
nfredexpath (univ⊃*ref nfunivδε _) (Red.appl univδε⇒EE') = nf-is-nf nfunivδε univδε⇒EE'
nfredexpath (univ⊃*ref _ nfrefχ) (Red.appr (Red.appl refχ⇒EE')) = nf-is-nf nfrefχ refχ⇒EE'
nfredexpath (univ⊃*ref _ _)(Red.appr (Red.appr ()))
nfredexpath (univ⊃*univ nfunivδε _)(Red.appl univδε⇒EE') = nf-is-nf nfunivδε univδε⇒EE'
nfredexpath (univ⊃*univ _ nfunivδ'ε')(Red.appr (Red.appl univδ'ε'⇒EE')) = nf-is-nf nfunivδ'ε' univδ'ε'⇒EE'
nfredexpath (univ⊃*univ _ _)(Red.appr (Red.appr ())) 
nfredexpath (ref⊃*ref nfrefφ _)(Red.appl refφ⇒EE') = nf-is-nf nfrefφ refφ⇒EE'
nfredexpath (ref⊃*ref _ nfrefψ)(Red.appr (Red.appl refψ⇒EE')) = nf-is-nf nfrefψ refψ⇒EE'
nfredexpath (ref⊃*ref _ _)(Red.appr (Red.appr ()))
nfredexpath (refref _ nfrefN)(Red.appl N⇒EE') = nf-is-nf nfrefN (Red.app (Red.appl N⇒EE'))
nfredexpath (refref _ nfrefN)(Red.appr (Red.appl N⇒EE')) = nf-is-nf nfrefN (Red.app (Red.appl N⇒EE'))
nfredexpath (refref nfrefM _)(Red.appr (Red.appr (Red.appl refM⇒EE'))) = nf-is-nf nfrefM refM⇒EE'
nfredexpath (refref _ nfrefN)(Red.appr (Red.appr (Red.appr (Red.appl refN⇒EE')))) = nf-is-nf nfrefN refN⇒EE'
nfredexpath (refref _ _)(Red.appr (Red.appr (Red.appr (Red.appr ()))))
nfredexpath (βE nfM _ _ _)(Red.appl M⇒EE') = nf-is-nf nfM M⇒EE'
nfredexpath (βE _ nfN _ _)(Red.appr (Red.appl N⇒EE')) = nf-is-nf nfN N⇒EE'
nfredexpath (βE _ _ nfΛAP _)(Red.appr (Red.appr (Red.appl ΛAP⇒EE'))) = nf-is-nf nfΛAP ΛAP⇒EE'
nfredexpath (βE _ _ _ nfQ)(Red.appr (Red.appr (Red.appr (Red.appl Q⇒EE')))) = nf-is-nf nfQ Q⇒EE'
nfredexpath (βE _ _ _ _)(Red.appr (Red.appr (Red.appr (Red.appr ()))))
nfredexpath (reflam nfN _ _ _ _)(Red.appl N⇒EE') = nf-is-nf nfN N⇒EE'
nfredexpath (reflam _ nfN' _ _ _)(Red.appr (Red.appl N'⇒EE')) = nf-is-nf nfN' N'⇒EE'
nfredexpath (reflam _ _ nfΛAM _ _)(Red.appr (Red.appr (Red.appl ΛAM⇒EE'))) = nf-is-nf nfΛAM ΛAM⇒EE'
nfredexpath (reflam _ _ _ nfP _)(Red.appr (Red.appr (Red.appr (Red.appl P⇒EE')))) = nf-is-nf nfP P⇒EE'
nfredexpath (reflam _ _ _ _ _)(Red.appr (Red.appr (Red.appr (Red.appr ()))))

postulate univ-osrE : ∀ {V} {φ} {ψ} {δ} {ε} {C : Path V → Set} →
                    (∀ φ' → φ Red.⇒ φ' → C (univ φ' ψ δ ε)) →
                    (∀ ψ' → ψ Red.⇒ ψ' → C (univ φ ψ' δ ε)) →
                    (∀ δ' → δ Red.⇒ δ' → C (univ φ ψ δ' ε)) →
                    (∀ ε' → ε Red.⇒ ε' → C (univ φ ψ δ ε')) →
                    ∀ {P} → univ φ ψ δ ε Red.⇒ P → C P
{- univ-osrE _ _ _ _ (redex ())
univ-osrE hypφ _ _ _ (app (appl φRed.⇒φ')) = hypφ _ φRed.⇒φ'
univ-osrE _ hypψ _ _ (app (appr (appl ψRed.⇒ψ'))) = hypψ _ ψRed.⇒ψ'
univ-osrE _ _ hypδ _ (app (appr (appr (appl δRed.⇒δ')))) = hypδ _ δRed.⇒δ'
univ-osrE _ _ _ hypε (app (appr (appr (appr (appl εRed.⇒ε'))))) = hypε _ εRed.⇒ε'
univ-osrE _ _ _ _ (app (appr (appr (appr (appr ()))))) -}

postulate eq-resp-conv : ∀ {V} {M M' N N' : Term V} {A : Type} →
                       M Red.≃ M' → N Red.≃ N' → M ≡〈 A 〉 N Red.≃ M' ≡〈 A 〉 N'
{- eq-resp-conv M≃M' N≃N' = app-resp-conv (trans-conv (convl M≃M') (convr (convl N≃N'))) -}

postulate R-creates-rep : Red.creates' REP

postulate R-respects-rep : Red.respects' REP

postulate osr-rep : ∀ {U} {V} {C} {K} {E E' : Subexp U C K} {ρ : Rep U V} →
                  E Red.⇒ E' → E 〈 ρ 〉 Red.⇒ E' 〈 ρ 〉
--osr-rep = aposrr REP R-respects-replacement

postulate red-rep : ∀ {U} {V} {C} {K} {E E' : Subexp U C K} {ρ : Rep U V} →
                  E Red.↠ E' → E 〈 ρ 〉 Red.↠ E' 〈 ρ 〉
-- red-rep = apredr REP R-respects-replacement

postulate conv-rep : ∀ {U V C K} {E E' : Subexp U C K} {ρ : Rep U V} → E Red.≃ E' → E 〈 ρ 〉 Red.≃ E' 〈 ρ 〉

postulate R-creates-replacement : Red.creates' REP

postulate R-respects-sub : Red.respects' SUB
postulate R₀-respects-sub : Red₀.respects' SUB

postulate osr-subl : ∀ {U} {V} {C} {K} {E F : Subexp U C K} {σ : Sub U V} → 
                    E Red.⇒ F → E ⟦ σ ⟧ Red.⇒ F ⟦ σ ⟧
--osr-subl = aposrr SUB R-respects-sub

postulate red-subl : ∀ {U} {V} {C} {K} {E F : Subexp U C K} {σ : Sub U V} → E Red.↠ F → E ⟦ σ ⟧ Red.↠ F ⟦ σ ⟧
--red-subl ERed.↠F = respects-red (aposrr SUB R-respects-sub) ERed.↠F

postulate red-subr : ∀ {U} {V} {C} {K} (E : Subexp U C K) {ρ σ : Sub U V} → ρ Red.↠s σ → E ⟦ ρ ⟧ Red.↠ E ⟦ σ ⟧
postulate red₀-subr : ∀ {U} {V} {C} {K} (E : Subexp U C K) {ρ σ : Sub U V} → ρ Red₀.↠s σ → E ⟦ ρ ⟧ Red₀.↠ E ⟦ σ ⟧

postulate ⊥SN : ∀ {V} → Red.SN {V} ⊥

postulate ⊃SN : ∀ {V} {φ ψ : Term V} → Red.SN φ → Red.SN ψ → Red.SN (φ ⊃ ψ)

postulate appT-red : ∀ {V} {M M' N N' : Term V} → M Red.↠ M' → N Red.↠ N' → appT M N Red.↠ appT M' N'

postulate SN-βexp : ∀ {V} {φ : Term V} {δ : Proof (V , -Proof)} {ε : Proof V} →
                        Red.SN ε → Red.SN (δ ⟦ x₀:= ε ⟧) → Red.SN (appP (ΛP φ δ) ε) 

postulate univ-red : ∀ {V} {φ φ' ψ ψ' : Term V} {δ} {δ'} {ε} {ε'} → 
                     φ Red.↠ φ' → ψ Red.↠ ψ' → δ Red.↠ δ' → ε Red.↠ ε' → univ φ ψ δ ε Red.↠ univ φ' ψ' δ' ε'

postulate ΛP-red : ∀ {V} {φ φ' : Term V} {δ} {δ'} → φ Red.↠ φ' → δ Red.↠ δ' → ΛP φ δ Red.↠ ΛP φ' δ'

postulate ⊃-red : ∀ {V} {φ φ' ψ ψ' : Term V} → φ Red.↠ φ' → ψ Red.↠ ψ' → φ ⊃ ψ Red.↠ φ' ⊃ ψ'
--⊃-red {V} {φ} {φ'} {ψ} {ψ'} φRed.↠φ' ψRed.↠ψ' = app-red (∷-red φRed.↠φ' (∷-redl ψRed.↠ψ'))

postulate appP-red : ∀ {V} {δ δ' ε ε' : Proof V} → δ Red.↠ δ' → ε Red.↠ ε' → appP δ ε Red.↠ appP δ' ε'
--appP-red δRed.↠δ' εRed.↠ε' = app-red (∷-red δRed.↠δ' (∷-redl εRed.↠ε'))

postulate ⊃*-red : ∀ {V} {P P' Q Q' : Path V} → P Red.↠ P' → Q Red.↠ Q' → (P ⊃* Q) Red.↠ (P' ⊃* Q')

postulate λλλ-red : ∀ {V A} {P Q : Path (V , -Term , -Term , -Path)} → P Red.↠ Q → λλλ A P Red.↠ λλλ A Q

postulate app*-red : ∀ {V} {M M' N N' : Term V} {P P' Q Q'} → M Red.↠ M' → N Red.↠ N' → P Red.↠ P' → Q Red.↠ Q' →
                   app* M N P Q Red.↠ app* M' N' P' Q'

postulate plus-red : ∀ {V} {P Q : Path V} → P Red.↠ Q → plus P Red.↠ plus Q

postulate ru-redex-half-red : ∀ {V} {φ φ' ψ ψ' : Term V} {δ δ'} →
                            φ Red.↠ φ' → ψ Red.↠ ψ' → δ Red.↠ δ' → ru-redex-half φ ψ δ Red.↠ ru-redex-half φ' ψ' δ'
--ru-redex-half-red φRed.↠φ' ψRed.↠ψ' δRed.↠δ' = ΛP-red (⊃-red φRed.↠φ' ψRed.↠ψ') (ΛP-red (red-rep φRed.↠φ') (appP-red (red-rep (red-rep δRed.↠δ')) ref))

ru-redex-red : ∀ {V} {φ φ' ψ ψ' χ χ' : Term V} δ δ' ε ε' →
  φ Red.↠ φ' → ψ Red.↠ ψ' → χ Red.↠ χ' → δ Red.↠ δ' → ε Red.↠ ε' →
  ru-redex φ ψ χ δ ε Red.↠ ru-redex φ' ψ' χ' δ' ε'
ru-redex-red _ _ _ _ φ↠φ' ψ↠ψ' χ↠χ' δ↠δ' ε↠ε' = univ-red (⊃-red φ↠φ' ψ↠ψ') (⊃-red φ↠φ' χ↠χ') (ru-redex-half-red φ↠φ' ψ↠ψ' δ↠δ') (ru-redex-half-red φ↠φ' χ↠χ' ε↠ε')

postulate ur-redex-half-red : ∀ {V} {φ φ' ψ ψ' : Term V} {χ χ' δ δ'} →
                            φ Red.↠ φ' → ψ Red.↠ ψ' → χ Red.↠ χ' → δ Red.↠ δ' →
                            ur-redex-half φ ψ χ δ Red.↠ ur-redex-half φ' ψ' χ' δ'
--ur-redex-half-red φ↠φ' ψ↠ψ' χ↠χ' δ↠δ' = ΛP-red (⊃-red φ↠φ' ψ↠ψ') (ΛP-red (red-rep χ↠χ') (appP-red ref (appP-red (red-rep (red-rep δ↠δ')) ref)))

postulate ur-redex-red : ∀ {V} {φ φ' ψ ψ' χ χ' : Term V} δ δ' ε ε' →
                       φ Red.↠ φ' → ψ Red.↠ ψ' → χ Red.↠ χ' → δ Red.↠ δ' → ε Red.↠ ε' →
                       ur-redex φ ψ χ δ ε Red.↠ ur-redex φ' ψ' χ' δ' ε'
--ur-redex-red {φ = φ} {φ'} {ψ} {ψ'} {χ} {χ'} _ _ _ _ φ↠φ' ψ↠ψ' χ↠χ' δ↠δ' ε↠ε' = univ-red (⊃-red φ↠φ' χ↠χ') (⊃-red ψ↠ψ' χ↠χ') (ur-redex-half-red φ↠φ' χ↠χ' ψ↠ψ' ε↠ε') (ur-redex-half-red ψ↠ψ' χ↠χ' φ↠φ' δ↠δ')

postulate uu-redex-half-red : ∀ {V} {φ φ₁ φ' φ'₁ ψ ψ₁ : Term V} {δ δ₁ ε ε₁} →
                            φ Red.↠ φ₁ → φ' Red.↠ φ'₁ → ψ Red.↠ ψ₁ → δ Red.↠ δ₁ → ε Red.↠ ε₁ →
                            uu-redex-half φ φ' ψ δ ε Red.↠ uu-redex-half φ₁ φ'₁ ψ₁ δ₁ ε₁
--uu-redex-half-red φ↠φ₁ φ'↠φ'₁ ψ↠ψ₁ δ↠δ₁ ε↠ε₁ = ΛP-red (⊃-red φ↠φ₁ φ'↠φ'₁) (ΛP-red (red-rep ψ↠ψ₁) (appP-red (red-rep (red-rep δ↠δ₁)) (appP-red ref (appP-red (red-rep (red-rep ε↠ε₁)) ref))))

postulate uu-redex-red : ∀ {V} {φ φ₁ φ' φ'₁ ψ ψ₁ ψ' ψ'₁ : Term V} δ {δ₁} δ' {δ'₁} ε {ε₁} ε' {ε'₁} →
                       φ Red.↠ φ₁ → φ' Red.↠ φ'₁ → ψ Red.↠ ψ₁ → ψ' Red.↠ ψ'₁ → δ Red.↠ δ₁ → δ' Red.↠ δ'₁ → ε Red.↠ ε₁ → ε' Red.↠ ε'₁ →
                       uu-redex φ φ' ψ ψ' δ δ' ε ε' Red.↠ uu-redex φ₁ φ'₁ ψ₁ ψ'₁ δ₁ δ'₁ ε₁ ε'₁
--uu-redex-red {φ = φ} {φ₁} {φ'} {φ'₁} {ψ} {ψ₁} {ψ'} {ψ'₁} _ _ _ _ φ↠φ₁ φ'↠φ'₁ ψ↠ψ₁ ψ'↠ψ'₁ δ↠δ₁ δ'↠δ'₁ ε↠ε₁ ε'↠ε'₁ = 
--  univ-red (⊃-red φ↠φ₁ φ'↠φ'₁) (⊃-red ψ↠ψ₁ ψ'↠ψ'₁) (uu-redex-half-red φ↠φ₁ φ'↠φ'₁ ψ↠ψ₁ δ'↠δ'₁ ε↠ε₁) (uu-redex-half-red ψ↠ψ₁ ψ'↠ψ'₁ φ↠φ₁ ε'↠ε'₁ δ↠δ₁)

postulate SNE : ∀ {V} {C} {K} (P : Subexp V C K → Set) →
              (∀ {M : Subexp V C K} → Red.SN M → (∀ N → M Red.↠⁺ N → P N) → P M) →
              ∀ {M : Subexp V C K} → Red.SN M → P M

private postulate var-red' : ∀ {V} {K} {x : Var V K} {M} {N} → M Red.↠ N → M ≡ var x → N ≡ var x
{-var-red' (inc (redex _)) ()
var-red' (inc (app _)) ()
var-red' ref M≡x = M≡x
var-red' (trans M↠N N↠P) M≡x = var-red' N↠P (var-red' M↠N M≡x) -}

postulate var-red : ∀ {V} {K} {x : Var V K} {M} → var x Red.↠ M → M ≡ var x
--var-red x↠M = var-red' x↠M refl

private postulate bot-red' : ∀ {V} {φ ψ : Term V} → φ Red.↠ ψ → φ ≡ ⊥ → ψ ≡ ⊥
{- bot-red' (inc (redex βT)) ()
bot-red' (inc (app {c = -bot} {F = []} x)) _ = refl
bot-red' (inc (app {c = -imp} _)) ()
bot-red' (inc (app {c = -appTerm} _)) ()
bot-red' (inc (app {c = -lamTerm _} _)) ()
bot-red' ref φ≡⊥ = φ≡⊥
bot-red' (trans φRed.↠ψ ψRed.↠χ) φ≡⊥ = bot-red' ψRed.↠χ (bot-red' φRed.↠ψ φ≡⊥) -}

postulate bot-red : ∀ {V} {φ : Term V} → ⊥ Red.↠ φ → φ ≡ ⊥
--bot-red ⊥Red.↠φ = bot-red' ⊥Red.↠φ refl

postulate imp-red' : ∀ {V} {φ ψ χ θ : Term V} → φ Red.↠ ψ → φ ≡ χ ⊃ θ →
                   Σ[ χ' ∈ Term V ] Σ[ θ' ∈ Term V ] χ Red.↠ χ' × θ Red.↠ θ' × ψ ≡ χ' ⊃ θ'
{-imp-red' (inc (redex βT)) ()
imp-red' (inc (app {c = -bot} _)) ()
imp-red' {θ = θ} (inc (app {c = -imp} (appl {E' = χ'} {F = _ ∷ []} χ⇒χ'))) φ≡χ⊃θ = 
  χ' ,p θ ,p subst (λ x → x Red.↠ χ') (⊃-injl φ≡χ⊃θ) (inc χ⇒χ') ,p 
  ref ,p (cong (λ x → χ' ⊃ x) (⊃-injr φ≡χ⊃θ))
imp-red' {χ = χ} (inc (app {c = -imp} (appr (appl {E' = θ'} {F = []} θ⇒θ')))) φ≡χ⊃θ = 
  χ ,p θ' ,p ref ,p (subst (λ x → x Red.↠ θ') (⊃-injr φ≡χ⊃θ) (inc θ⇒θ')) ,p 
  cong (λ x → x ⊃ θ') (⊃-injl φ≡χ⊃θ)
imp-red' (inc (app {c = -imp} (appr (appr ())))) _
imp-red' (inc (app {c = -appTerm} _)) ()
imp-red' (inc (app {c = -lamTerm _} _)) ()
imp-red' {χ = χ} {θ} ref φ≡χ⊃θ = χ ,p θ ,p ref ,p ref ,p φ≡χ⊃θ
imp-red' (trans φRed.↠ψ ψRed.↠ψ') φ≡χ⊃θ = 
  let (χ' ,p θ' ,p χRed.↠χ' ,p θRed.↠θ' ,p ψ≡χ'⊃θ') = imp-red' φRed.↠ψ φ≡χ⊃θ in 
  let (χ'' ,p θ'' ,p χ'Red.↠χ'' ,p θ'Red.↠θ'' ,p ψ'≡χ''⊃θ'') = imp-red' ψRed.↠ψ' ψ≡χ'⊃θ' in 
  χ'' ,p θ'' ,p RTClose.trans χRed.↠χ' χ'Red.↠χ'' ,p RTClose.trans θRed.↠θ' θ'Red.↠θ'' ,p ψ'≡χ''⊃θ''-}

postulate imp-red : ∀ {V} {χ θ ψ : Term V} → χ ⊃ θ Red.↠ ψ →
                  Σ[ χ' ∈ Term V ] Σ[ θ' ∈ Term V ] χ Red.↠ χ' × θ Red.↠ θ' × ψ ≡ χ' ⊃ θ'
--imp-red χ⊃θRed.↠ψ = imp-red' χ⊃θRed.↠ψ refl

postulate conv-sub : ∀ {U} {V} {C} {K} {σ : Sub U V} {M N : Subexp U C K} → M Red.≃ N → M ⟦ σ ⟧ Red.≃ N ⟦ σ ⟧

postulate appT-convl : ∀ {V} {M M' N : Term V} → M Red.≃ M' → appT M N Red.≃ appT M' N

data redVT {V} : ∀ {n} → snocVec (Term V) n → snocVec (Term V) n → Set where
  redleft : ∀ {n} {MM MM' : snocVec (Term V) n} {N} → redVT MM MM' → redVT (MM snoc N) (MM' snoc N)
  redright : ∀ {n} {MM : snocVec (Term V) n} {N N'} → N Red.⇒ N' → redVT (MM snoc N) (MM snoc N')

data osrVP {V} : ∀ {n} → snocVec (Proof V) n → snocVec (Proof V) n → Set where
  redleft : ∀ {n} {εε εε' : snocVec _ n} {δ} → osrVP εε εε' → osrVP (εε snoc δ) (εε' snoc δ)
  redright : ∀ {n} {εε : snocVec _ n} {δ} {δ'} → δ Red.⇒ δ' → osrVP (εε snoc δ) (εε snoc δ')

data osrVPa {V} : ∀ {n} → snocVec (Path V) n → snocVec (Path V) n → Set where
  redleft : ∀ {n} {PP PP' : snocVec (Path V) n} {Q} → osrVPa PP PP' → osrVPa (PP snoc Q) (PP' snoc Q)
  redright : ∀ {n} {PP : snocVec (Path V) n} {Q Q'} → Q Red.⇒ Q' → osrVPa (PP snoc Q) (PP snoc Q')

postulate APPP-osrl : ∀ {V n δ δ'}  → δ Red.⇒ δ' → ∀ (εε : snocVec (Proof V) n) → APPP δ εε Red.⇒ APPP δ' εε
{-APPP-osrl {εε = []} δRed.⇒δ' = δRed.⇒δ'
APPP-osrl {εε = εε snoc _} δRed.⇒δ' = app (appl (APPP-osrl {εε = εε} δRed.⇒δ'))-}

postulate APPP-osrr : ∀ {V n δ} {εε εε' : snocVec (Proof V) n} → osrVP εε εε' → APPP δ εε Red.⇒ APPP δ εε'

postulate APPP-redl : ∀ {V n δ δ'}  → δ Red.↠ δ' → ∀ (εε : snocVec (Proof V) n) → APPP δ εε Red.↠ APPP δ' εε

postulate APP*-osr₁ : ∀ {V n} {MM MM' NN : snocVec (Term V) n} {P PP} → redVT MM MM' → APP* MM NN P PP Red.⇒ APP* MM' NN P PP
--APP*-osr₁ {NN = _ snoc _} {PP = _ snoc _} (osrleft MMRed.⇒MM') = app (appr (appr (appl (APP*-osr₁ MMRed.⇒MM'))))
--APP*-osr₁ {NN = _ snoc _} {PP = _ snoc _} (osrright MRed.⇒M') = app (appl MRed.⇒M')

postulate APP*-osr₂ : ∀ {V n} MM {NN NN' : snocVec (Term V) n} {P PP} → redVT NN NN' → APP* MM NN P PP Red.⇒ APP* MM NN' P PP
--APP*-osr₂ (MM snoc _) {_ snoc _} {_ snoc _} {PP = _ snoc _} (osrleft NNRed.⇒NN') = app (appr (appr (appl (APP*-osr₂ MM NNRed.⇒NN'))))
--APP*-osr₂ (_ snoc _) {PP = _ snoc _} (osrright NRed.⇒N') = app (appr (appl NRed.⇒N'))

postulate APP*-osr₃ : ∀ {V n} MM {NN : snocVec (Term V) n} {P P' PP} → P Red.⇒ P' → APP* MM NN P PP Red.⇒ APP* MM NN P' PP
--APP*-osr₃ [] {[]} {PP = []} PRed.⇒P' = PRed.⇒P'
--APP*-osr₃ (MM snoc M) {NN snoc N} {PP = PP snoc P} PRed.⇒P' = app (appr (appr (appl (APP*-osr₃ MM PRed.⇒P'))))

postulate APP*-osr₄ : ∀ {V n} MM {NN : snocVec (Term V) n} {P PP QQ} → osrVPa PP QQ → APP* MM NN P PP Red.⇒ APP* MM NN P QQ

APP*-red₃ : ∀ {V n} MM {NN : snocVec (Term V) n} {P P' PP} → P Red.↠ P' → APP* MM NN P PP Red.↠ APP* MM NN P' PP
APP*-red₃ MM (inc P⇒P') = inc (APP*-osr₃ MM P⇒P')
APP*-red₃ MM ref = ref
APP*-red₃ MM (trans P₁↠P₂ P₂↠P₃) = RTClose.trans (APP*-red₃ MM P₁↠P₂) (APP*-red₃ MM P₂↠P₃)

nf-SN : ∀ {V} {M : Term V} → nf M → Red.SN M
nf-SN nfM = Red.SNI _ (λ M' M⇒M' → ⊥-elim (nf-is-nf nfM M⇒M'))

βsub : ∀ {U V A} M {σ : Sub U V} {N} → appT (ΛT A M ⟦ σ ⟧) N Red.⇒ M ⟦ extendSub σ N ⟧
βsub {U} {V} {A} M {σ} {N} = subst (λ x → appT (ΛT A M ⟦ σ ⟧) N Red.⇒ x) (Prelims.sym (extendSub-decomp M)) (Red.redex (βR βT))
