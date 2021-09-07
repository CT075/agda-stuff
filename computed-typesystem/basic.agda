open import Data.Nat
open import Data.Bool hiding (T)
open import Data.Maybe

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

variable
  T : Set

record ∃ (A : Set) (B : A -> Set) : Set where
  constructor pack
  field
    proj₁ : A
    proj₂ : B proj₁

syntax ∃ A (λ x → B) = ∃[ x ∶ A ] B

unpack : ∀{A B} -> ∃ A B -> ((proj₁ : A) -> B proj₁ -> T) -> T
unpack (pack proj₁ proj₂) f = f proj₁ proj₂

---- Source language

data Exp : Set where
  valB : Bool -> Exp
  valN : ℕ -> Exp
  add : Exp -> Exp -> Exp
  if : Exp -> Exp -> Exp -> Exp

---- Typing
infix 4 ⊢_∶_

data Ty : Set where
  nat : Ty
  bool : Ty

denot : Ty -> Set
denot nat = ℕ
denot bool = Bool

data ⊢_∶_ : Exp -> Ty -> Set where
  typ-bool : ∀{b : Bool} -> ⊢(valB b) ∶ bool
  typ-int : ∀{i : ℕ} -> ⊢(valN i) ∶ nat
  typ-add : ∀{e1 : Exp} {e2 : Exp} ->
    ⊢ e1 ∶ nat -> ⊢ e2 ∶ nat -> ⊢ (add e1 e2) ∶ nat
  typ-if : ∀{τ} {e : Exp} {e1 : Exp} {e2 : Exp} ->
    ⊢ e ∶ bool -> ⊢ e1 ∶ τ -> ⊢ e2 ∶ τ -> ⊢ (if e e1 e2) ∶ τ

matchType : (τ1 : Ty) -> (τ2 : Ty) -> Maybe (τ1 ≡ τ2)
matchType nat nat = just refl
matchType bool bool = just refl
matchType _ _ = nothing

matchTypeEquiv : ∀{τ : Ty} -> (matchType τ τ ≡ just refl)
matchTypeEquiv {nat} = refl
matchTypeEquiv {bool} = refl

synthtype : Exp -> Maybe Ty
synthtype (valB _) = just bool
synthtype (valN _) = just nat
synthtype (add e1 e2) =
  synthtype e1 >>= (λ τ1 ->
    matchType τ1 nat >>= (λ _ ->
      synthtype e2 >>= (λ τ2 ->
        matchType τ2 nat >>= (λ _ ->
          just nat
        ))))
synthtype (if e e1 e2) =
  synthtype e >>= (λ τ ->
    matchType τ bool >>= (λ _ ->
      synthtype e1 >>= (λ τ1 ->
        synthtype e2 >>= (λ τ2 ->
          matchType τ1 τ2 >>= (λ _ ->
            just τ1
          )))))

typeCorrectLHS : ∀{e : Exp}{τ : Ty} -> ⊢ e ∶ τ -> (synthtype e ≡ just τ)
typeCorrectLHS {valB _} {bool} typ-bool = refl
typeCorrectLHS {valN _} {nat} typ-int = refl
typeCorrectLHS {add e1 e2} {nat} (typ-add p1 p2) = begin
    synthtype (add e1 e2)
  ≡⟨ refl ⟩ -- definition
    (synthtype e1 >>= (λ τ1 -> matchType τ1 nat >>= (λ _ ->
      synthtype e2 >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))))
  ≡⟨ cong
      (λ n -> n >>= (λ τ1 -> matchType τ1 nat >>= (λ _ ->
        synthtype e2 >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))))
      (typeCorrectLHS {e1} {nat} p1) ⟩ -- IH e1
    (just nat >>= (λ τ1 -> matchType τ1 nat >>= (λ _ ->
      synthtype e2 >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))))
  ≡⟨ refl ⟩ -- definition of (>>=) and matchType
    (synthtype e2 >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))
  ≡⟨ cong
      (λ n -> n >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))
      (typeCorrectLHS {e2} {nat} p2) ⟩ -- IH e2
    (just nat >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))
  ≡⟨ refl ⟩
    just nat
  ∎
typeCorrectLHS {if e e1 e2} {τ} (typ-if p p1 p2) = begin
    synthtype (if e e1 e2)
  ≡⟨ refl ⟩ -- definition
    (synthtype e >>= (λ τ ->
      matchType τ bool >>= (λ _ ->
        synthtype e1 >>= (λ τ1 ->
          synthtype e2 >>= (λ τ2 ->
            matchType τ1 τ2 >>= (λ _ ->
              just τ1))))))
  ≡⟨ cong
       (λ n -> n >>= (λ τ ->
         matchType τ bool >>= (λ _ ->
           synthtype e1 >>= (λ τ1 ->
             synthtype e2 >>= (λ τ2 ->
               matchType τ1 τ2 >>= (λ _ ->
                 just τ1))))))
       (typeCorrectLHS {e} {bool} p)⟩ -- IH e
     (just bool >>= (λ τ ->
       matchType τ bool >>= (λ _ ->
         synthtype e1 >>= (λ τ1 ->
           synthtype e2 >>= (λ τ2 ->
             matchType τ1 τ2 >>= (λ _ ->
               just τ1))))))
  ≡⟨ refl ⟩ -- definition of (>>=) and matchType
     (synthtype e1 >>= (λ τ1 ->
       synthtype e2 >>= (λ τ2 ->
         matchType τ1 τ2 >>= (λ _ -> just τ1))))
  ≡⟨ cong
       (λ n -> n >>= (λ τ1 ->
         synthtype e2 >>= (λ τ2 ->
           matchType τ1 τ2 >>= (λ _ -> just τ1))))
       (typeCorrectLHS {e1} {τ} p1) ⟩ -- IH e1
     (just τ >>= (λ τ1 ->
       synthtype e2 >>= (λ τ2 ->
         matchType τ1 τ2 >>= (λ _ -> just τ1))))
  ≡⟨ refl ⟩
     (synthtype e2 >>= (λ τ2 ->
       matchType τ τ2 >>= (λ _ -> just τ)))
  ≡⟨ cong
       (λ n -> n >>= (λ τ2 -> matchType τ τ2 >>= (λ _ -> just τ)))
       (typeCorrectLHS {e2} {τ} p2) ⟩ -- IH e2
     (just τ >>= (λ τ2 -> matchType τ τ2 >>= (λ _ -> just τ)))
  ≡⟨ refl ⟩
     (matchType τ τ >>= (λ _ -> just τ))
  ≡⟨ cong (λ n -> n >>= (λ _ -> just τ)) (matchTypeEquiv {τ}) ⟩
     (just (refl {x = τ}) >>= (λ _ -> just τ))
  ≡⟨ refl ⟩
     just τ
  ∎
