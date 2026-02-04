module ch3 where

open import ch2 public


data ℕ : Set where
  0ℕ : ℕ
  succℕ : ℕ → ℕ

1ℕ = succℕ 0ℕ
2ℕ = succℕ 1ℕ
3ℕ = succℕ 2ℕ
4ℕ = succℕ 3ℕ
5ℕ = succℕ 4ℕ
6ℕ = succℕ 5ℕ
7ℕ = succℕ 6ℕ
8ℕ = succℕ 7ℕ
9ℕ = succℕ 8ℕ
10ℕ = succℕ 9ℕ
11ℕ = succℕ 10ℕ
12ℕ = succℕ 11ℕ
13ℕ = succℕ 12ℕ
14ℕ = succℕ 13ℕ
15ℕ = succℕ 14ℕ
16ℕ = succℕ 15ℕ
17ℕ = succℕ 16ℕ
18ℕ = succℕ 17ℕ
19ℕ = succℕ 18ℕ
20ℕ = succℕ 19ℕ

indℕ : {P : ℕ → Set} → (P 0ℕ) → ((n : ℕ) → (P n → P (succℕ n))) → (m : ℕ) → P m
indℕ {P} x f 0ℕ = x
indℕ {P} x f (succℕ m) = f m (indℕ x f m)

-- 3.2 Addition
infixl 6 _+ℕ_
_+ℕ_ : ℕ → ℕ → ℕ
n +ℕ 0ℕ = n
n +ℕ succℕ m = succℕ (n +ℕ m)

-- Exercises
-- 3.1
infixl 7 _·ℕ_
_·ℕ_ : ℕ → ℕ → ℕ
n ·ℕ 0ℕ = 0ℕ
n ·ℕ succℕ m = n +ℕ (n ·ℕ m)

infixr 8 _^ℕ_
_^ℕ_ : ℕ → ℕ → ℕ
n ^ℕ 0ℕ = 1ℕ
n ^ℕ succℕ m = n ·ℕ (n ^ℕ m)

-- 3.2
minℕ : ℕ → ℕ → ℕ
minℕ n 0ℕ = 0ℕ
minℕ 0ℕ (succℕ m) = 0ℕ
minℕ (succℕ n) (succℕ m) = succℕ (minℕ n m)

maxℕ : ℕ → ℕ → ℕ
maxℕ n 0ℕ = n
maxℕ 0ℕ (succℕ m) = succℕ m
maxℕ (succℕ n) (succℕ m) = succℕ (maxℕ n m)

-- 3.3
triangleℕ : ℕ → ℕ
triangleℕ 0ℕ = 0ℕ
triangleℕ (succℕ n) = succℕ n +ℕ triangleℕ n

factorialℕ : ℕ → ℕ
factorialℕ 0ℕ = 1ℕ
factorialℕ (succℕ n) = succℕ n ·ℕ factorialℕ n

-- 3.4
choose : ℕ → ℕ → ℕ
choose n 0ℕ = 1ℕ
choose 0ℕ (succℕ k) = 0ℕ
choose (succℕ n) (succℕ k) = (choose n k) +ℕ (choose n (succℕ k))

-- 3.5
fibℕ : ℕ → ℕ
fibℕ 0ℕ = 0ℕ
fibℕ (succℕ 0ℕ) = 1ℕ
fibℕ (succℕ (succℕ n)) = fibℕ n +ℕ fibℕ (succℕ n)

-- 3.6
div-twoℕ : ℕ → ℕ
div-twoℕ 0ℕ = 0ℕ
div-twoℕ (succℕ 0ℕ) = 0ℕ
div-twoℕ (succℕ (succℕ n)) = succℕ (div-twoℕ n)
