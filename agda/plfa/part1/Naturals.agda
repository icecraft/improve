
module plfa.part1.Naturals where


data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ


two : ℕ
two  = suc ( suc zero )      

three : ℕ
three = suc two
        
    
{-# BUILTIN NATURAL ℕ #-}    
        
    
    
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

    
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- 展开为
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- 归纳步骤
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- 归纳步骤
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- 起始步骤
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- 简写为
    5
  ∎
    


-- why ?    
_ : 3 + 3 ≡ 6
_ = refl      


_ : 3 + 4 ≡  7
_ = begin
      3 + 4
    ≡⟨⟩      
      suc ( 2 + 4 )
    ≡⟨⟩   
      suc ( suc ( 1 + 4 ))
    ≡⟨⟩                  
      suc ( suc ( suc ( 0 + 4 )))
    ≡⟨⟩
      suc ( suc ( suc 4 ) ) 
    ≡⟨⟩
       7
     ∎

    

{- mul -}
    
_*_ :  ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)


mulByOne_ : ℕ -> ℕ
mulByOne n = 1 * n     

    
_ : 3 * 4 ≡  12
_ = begin
      3 * 4
    ≡⟨⟩
      4 + ( 2 * 4 )
    ≡⟨⟩
      4 + ( 4 + ( 1 * 4 ))   -- 如果可以定义 1 * m = m, 则可以简化证明步骤. 1 * m = m 算是引理, 问题就变成了如何在函数中使用引理
    ≡⟨⟩
      4 + ( 4 + ( 4 + ( 0 * 4) ) )
    ≡⟨⟩
      4 + ( 4 + ( 4 + 0 ))
    ≡⟨⟩
      4 + ( 4 + 4 )
    ≡⟨⟩
      4 + 8
    ≡⟨⟩
      12
   ∎


-- how to define functions with the help of existed functions ?    
-- oneM*_ : ∀ {n} →  ℕ  → ℕ  

           
_^_ :  ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * ( n ^ m )


_∸_ : ℕ → ℕ → ℕ
m ∸  zero = m
zero  ∸  n = zero
suc m ∸  suc n = m ∸ n



{- more prama -}        
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}
            
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

    
{- 不知道如何实现
  to : ℕ -> Bin
  to zero = () O
-}            
    
            
    

    
           
    

    
    
     
        

        
