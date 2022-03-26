

module plfa.part1.Induction where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)




-- * and /


-- vector 的 + 和 *


_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎


                
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
    begin
       (zero + n) + p
    ≡⟨⟩
      n + p
    ≡⟨⟩ zero + ( n + p )
    ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎


+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
    begin
      zero + zero
    ≡⟨⟩
      zero
    ∎
+-identityʳ (suc m) =
    begin
      suc m + zero
    ≡⟨⟩
      suc ( m + zero )
    ≡⟨ cong suc (+-identityʳ m) ⟩
      suc m
    ∎
        
    
            
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
    begin
      zero + suc n
    ≡⟨⟩
     suc n
    ≡⟨⟩
     suc (zero + n)
    ∎
+-suc (suc m) n =
    begin
      suc m  + suc n
    ≡⟨⟩
      suc (m + suc n)    
    ≡⟨ cong suc (+-suc m n) ⟩
      suc (suc (m + n))
    ≡⟨⟩
     suc (suc m + n)
    ∎
     
                  

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
    begin
       m + zero
    ≡⟨ +-identityʳ m ⟩
      m
    ≡⟨⟩
      zero + m
    ∎
+-comm m (suc n) =
    begin
      m + suc n
    ≡⟨ +-suc m n ⟩
      suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
       suc ( n + m)
    ≡⟨⟩
      suc n + m
    ∎
               
-- 什么时候使用 cong, 什么时候不需要使用 cong ?            
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
     (m + n ) + (p + q)
    ≡⟨ +-assoc m n (p + q) ⟩
       m + (n + (p + q))
    ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
      m + (( n + p ) + q)
    ≡⟨ sym (+-assoc m (n + p) q) ⟩
      (m + (n + p)) + q
    ≡⟨⟩
     m + (n + p) + q
    ∎
    
    
    
     
    
    
