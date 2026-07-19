
module Cubical.Data.Rationals.MoreRationals.NormalisedQ.MoreProperties where

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit

open import Cubical.Data.Nat as ℕ using (ℕ; suc; zero; predℕ; snotz; znots)
  renaming (_+_ to _ℕ+_; _·_ to _ℕ·_)
open import Cubical.Data.Nat.GCD as ℕ renaming (gcd to gcdℕ; gcdSym to gcdℕSym)
open import Cubical.Data.Nat.Coprime
open import Cubical.Data.Nat.Mod
open import Cubical.Data.NatPlusOne.PropertiesWithInt
  using (ℕ₊₁→ℤ; ·ℕ₊₁→ℤ-distr )

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.HITs.SetQuotients using (eq/)
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.Data.Sigma
open import Cubical.Data.Sum.Base
open import Cubical.Data.Int.Order as ℤ using ()
open import Cubical.Data.Int as ℤ
  using (ℤ; pos; negsuc; isIntegralℤ; injPos)
  renaming (-_ to -ℤ_; ·IdR to ℤ·IdR; ·IdL to ℤ·IdL; +Assoc to ℤ+Assoc;
   ·Assoc to ℤ·Assoc; ·Comm to ℤ·Comm; ·DistR+ to ℤ·DistR+;
   ·DistL+ to ℤ·DistL+; -DistL· to ℤ-DistL·; abs to absℤ;
   abs· to absℤ·)
open import Cubical.Data.Int.GCD as ℤ

open import Cubical.Data.Bool hiding (_≤_; _≥_)
open import Cubical.Data.NatPlusOne as ℕ₊₁
  using (1+_; _·₊₁_; ℕ₊₁; ℕ₊₁→ℕ; ℕ₊₁→ℕ-inj; ·₊₁-comm; -1+_;
    ·₊₁-identityʳ; ·₊₁-identityˡ ; ·₊₁-assoc)

open import Cubical.Data.Rationals.MoreRationals.NormalisedQ
open import Cubical.Data.Rationals.MoreRationals.NormalisedQ.Order

private
  variable
    m n o : ℚ

----------------------------------------
-- BASE ???? ****

≡Dec : ∀ (p q : ℚ) → Dec (p ≡ q)
≡Dec p q = discreteℚ p q

≃Dec : ∀ (p q : ℚ) → Dec (p ≃ q)  -- remove other Dec? *****
≃Dec p q = dec≃ {p}{q}

¬*≡* : ∀ {m}{n} → ¬ (↥ m) ℤ.· (↧ n) ≡ (↥ n) ℤ.· (↧ m) → ¬ m ≃ n
¬*≡* {m}{n} ¬mn = λ x → ¬mn (*≡*⁻¹ {m}{n} x)

sym≄ : ∀ {m}{n} → (m ≄ n) → (n ≄ m)
sym≄ {m}{n} mn = λ x → mn (sym≃ x)

-- ℤ.Order

ℤweaken≡→≤ : ∀ {m}{n} → m ≡ n → m ℤ.≤ n
ℤweaken≡→≤ {m}{n} mn =
  subst (λ x → x) (cong (λ x → x ℤ.≤ n) (sym mn)) (ℤ.isRefl≤ {n})

ℤspecialise¬≤→¬≡ : ∀ {m n : ℤ} → ¬ m ℤ.≤ n → ¬ m ≡ n
ℤspecialise¬≤→¬≡ {m}{n} ¬mn = λ x → ¬mn (ℤweaken≡→≤ x)

ℤ<→¬≡ : ∀ {m n : ℤ} → m ℤ.< n → ¬ m ≡ n
ℤ<→¬≡ {m}{n} m<n m≡n =
  ⊥.elim (ℤ.isAsym< {m}{n} m<n (subst (λ u → u ℤ.≤ m) m≡n (ℤ.isRefl≤ {m})))


----------------------------------------

infix 4 _<_ _≥_ _>_ _⋖_ _⋗_

_<_ : ℚ → ℚ → Type
m < n = (↥ m ℤ.· ↧ n) ℤ.< (↥ n ℤ.· ↧ m)

_⋖_ : ℚ → ℚ → Type
m ⋖ n = (m ≤ n) × (¬ m ≃ n)

_≥_ : ℚ → ℚ → Type
m ≥ n = n ≤ m

_>_ : ℚ → ℚ → Type
m > n = n < m

_⋗_ : ℚ → ℚ → Type
m ⋗ n = (m ≥ n) × (¬ m ≃ n)

<→¬≃ : m < n → ¬ m ≃ n
<→¬≃ {m}{n} m<n = ¬*≡* (ℤ<→¬≡ m<n)

isIrrefl< : ¬ m < m
isIrrefl< = ℤ.isIrrefl<

<-weaken : m < n → m ≤ n
<-weaken m<n = ℤ.<-weaken m<n

<→¬≡ : m < n → ¬ m ≡ n
<→¬≡ {m}{n} m<n = ≄→¬≡ (<→¬≃ m<n)

<→⋖ : m < n → m ⋖ n
<→⋖ {m}{n} mn = (<-weaken {m}{n} mn) , (<→¬≃ mn)

¬<→¬⋖ : ¬ (m < n) → ¬ (m ⋖ n)
¬<→¬⋖ {m} {n} ¬mn ((zero , mn) , ¬m≃n) = ¬m≃n (*≡* mn)
¬<→¬⋖ {m} {n} ¬mn ((suc d , mn) , ¬m≃n) =
  ¬mn (ℤ.<-+pos-trans {(↥ m) ℤ.· (↧ n)} {d}{(↥ n) ℤ.· (↧ m)} (zero , mn))

<Stable : Stable (m < n)
<Stable {m}{n} ¬¬m<n = ℤ.<Stable (↥ m ℤ.· ↧ n) (↥ n ℤ.· ↧ m) ¬¬m<n

⋖→< : m ⋖ n → m < n
⋖→< {m}{n} mn = <Stable {m}{n} (converse ¬<→¬⋖ (λ z → z mn))

⋖Dec : ∀ m n → Dec (m ⋖ n)
⋖Dec m n with ≤Dec m n | ≃Dec m n
... | yes m | yes n = no (λ z → z .snd n)
... | yes m | no ¬n = yes (m , ¬n)
... | no ¬m | yes n = no (λ z → ¬m (z .fst))
... | no ¬m | no ¬n = no (λ z → ¬m (z .fst))

<Dec : ∀ (m n : ℚ) → Dec (m < n)
<Dec m n with ⋖Dec m n
... | yes p = yes (⋖→< p)
... | no ¬p = no (converse <→⋖ ¬p)

≥Dec : ∀ (m n : ℚ) → Dec (m ≥ n)
≥Dec m n = ≤Dec n m

>Dec : ∀ (m n : ℚ) → Dec (m > n)
>Dec m n = <Dec n m

{- data Trichotomy (m n : ℚ) : Type₀ where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

trichotomy-diff :  ∀ {m n} → Trichotomy m n → ℚ
trichotomy-diff {m}{n} (lt (k , _)) = [ pos (suc k) , ↧₊₁ m ·₊₁ ↧₊₁ n ]
trichotomy-diff {m}{n} (eq x) = 0ℚ
trichotomy-diff {m} {n} (gt (k , _)) = [ negsuc k ,  ↧₊₁ m ·₊₁ ↧₊₁ n ]

trichotomy-diff≡ : ∀ {m n} → (mn : Trichotomy m n) → m + (trichotomy-diff mn) ≡ n
trichotomy-diff≡ {m}{n} (lt x) = {!!}
  where
    step : m < n
    step = x
trichotomy-diff≡ {m}{n} (eq x) = {!!}
trichotomy-diff≡ {m}{n} (gt x) = {!!}  -}

xxx = ℤ.≤-o+-cancel

yyy = ·[]CancelR

≤-diff : ∀ {m n} → m ≤ n → Σ[ d ∈ ℚ ] (m + d ≡ n) × NonNegative d
≤-diff {m}{n} (k , eqn) = {!!}
  where
    d'' = n - m
    d' = normalise k (↧₊₁ m ·₊₁ ↧₊₁ n)
    eqn' : (((↥ m) ℤ.· (↧ n)) ℤ.+pos k) ≡ (↥ n) ℤ.· (↧ m)
    eqn' = eqn
    help : [ ↥ n ℤ.· ↧ m , 1 ·₊₁ ↧₊₁ m ] ≡ [ ↥ n , 1 ]
    help = ·[]CancelR {↥ n}{1} (1+ m .fst .snd)
    help2 : [ ↥ n ℤ.· ↧ m , ↧₊₁ n ·₊₁ ↧₊₁ m ] ≡ [ ↥ n , ↧₊₁ n ]
    help2 = ·[]CancelR {↥ n}{↧₊₁ n} (↧₊₁ m)
    eqn1 : [ (↥ m ℤ.· ↧ n) ℤ.+pos k , 1 ] ≡ [ ↥ n ℤ.· ↧ m , 1 ]
    eqn1 = cong (λ u → [ u , 1 ]) eqn
    eqn2 : [ (↥ m ℤ.· ↧ n) ℤ.+pos k , ↧₊₁ m ] ≡ [ ↥ n , 1 ]
    eqn2 = {!!}
    help3 : [ (↥ m ℤ.· ↧ n) ℤ.+pos k , ↧₊₁ n ·₊₁ ↧₊₁ m ] ≡ [ ↥ n ℤ.· ↧ m , ↧₊₁ n ·₊₁ ↧₊₁ m ]
    help3 = cong (λ u → [ u , ↧₊₁ n ·₊₁ ↧₊₁ m ]) eqn

≤-+o : m ≤ n → m + o ≤ n + o
≤-+o {m}{n}{o} (k , eqn) = {!!}

≤-o+ : m ≤ n → o + m ≤ o + n
≤-o+ {m} {n} {o} (k , eqn) = {!!}

≤-o+-cancel : o + m ≤ o + n → m ≤ n
≤-o+-cancel {o}{m} mon = {!!}

m≤n→¬n<m : ∀ {m n} → m ≤ n → ¬ (n < m)
m≤n→¬n<m {m}{n} mn =
  converse (ℤ.isAsym< {↥ n ℤ.· ↧ m} {↥ m ℤ.· ↧ n}) λ z → z mn

¬m<n→n≤m : ∀ {m n : ℚ} → ¬ (m < n) → n ≤ m
¬m<n→n≤m {m}{n} ¬mn with (↥ m ℤ.· ↧ n) ℤ.≟ (↥ n ℤ.· ↧ m)
... | ℤ.lt x = ⊥.elim (¬mn x)
... | ℤ.eq x = zero , sym x
... | ℤ.gt x = ℤ.<-weaken x

¬m≤n→n<m : ∀ {m n : ℚ} → ¬ (m ≤ n) → n < m
¬m≤n→n<m {m}{n} ¬m≤n = ⋖→< {n}{m}
  (¬m<n→n≤m {m}{n} (converse (<-weaken {m}{n}) ¬m≤n) ,
   sym≄ (¬*≡* (ℤspecialise¬≤→¬≡ ¬m≤n)))

m≤n→n≤m→m≃n : ∀ {m n} → m ≤ n → n ≤ m → m ≃ n
m≤n→n≤m→m≃n {m}{n} m≤n n≤m = *≡* (ℤ.isAntisym≤ m≤n n≤m)

isRefl≤ : ∀ m → m ≤ m
isRefl≤ m = zero , refl

isAntisym≤ : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
isAntisym≤ {m}{n} m≤n n≤m = ≃→≡ (m≤n→n≤m→m≃n m≤n n≤m)

isTrans≤ : m ≤ n → n ≤ o → m ≤ o
isTrans≤ {m}{n}{o} mn n≤o = (fst mn ℕ+ fst n≤o) , {!!}
  where
    step = ℤ.isTrans≤ { (↥ m ℤ.· ↧ n)} mn {!!}

weaken≡→≤ : m ≡ n → m ≤ n
weaken≡→≤ mn = zero , *≡*⁻¹ (≡→≃ mn)

n⋖m→¬m⋖n : ∀ {m n} → m ⋖ n → ¬ (n ⋖ m)
n⋖m→¬m⋖n {m}{n} m⋖n n⋖m = (snd m⋖n) (m≤n→n≤m→m≃n  (m⋖n .fst) (n⋖m .fst))



----------------------------------------

infixl 8 _^_ _**_
infixl 7 _⊓_
infixl 6 _⊔_

-- Min
_⊓_ : ℚ → ℚ → ℚ
p ⊓ q with (≤Dec p q)
... | yes p' = p
... | no q' = q

min = _⊓_

p⊓q-def1 : ∀ {p q : ℚ} → p ≤ q → p ⊓ q ≡ p
p⊓q-def1 {p}{q} pq with ≤Dec p q
... | yes r = refl
... | no ¬r = ⊥.elim {A = λ x → q ≡ p} (¬r pq)

p⊓q-def2 : ∀ {p q : ℚ} → p ⊓ q ≡ p → p ≤ q
p⊓q-def2 {p}{q} pq with ≤Dec p q
... | yes r = r
... | no ¬r = zero , *≡*⁻¹ (≡→≃ (sym pq))

-- Max
_⊔_ : ℚ → ℚ → ℚ
p ⊔ q with (≤Dec p q)
... | yes p' = q
... | no q' = p

max = _⊔_

-- -⊔≡⊓ ∀ {p q : ℚ} → p ⊔ q ≡ p ⊓ q

p⊔q-def1 : ∀ {p q : ℚ} → p ≤ q → p ⊔ q ≡ q
p⊔q-def1 {p}{q} pq with ≤Dec p q
... | yes r = refl
... | no ¬r = ⊥.elim {A = λ x → p ≡ q} (¬r pq)

p⊔q-def2 : ∀ {p q : ℚ} → p ⊔ q ≡ p → q ≤ p
p⊔q-def2 {p}{q} pq with ≤Dec p q
... | yes r = weaken≡→≤ pq
... | no ¬r = <-weaken {q}{p} (¬m≤n→n<m {p}{q} ¬r)

-- Any ℚ to the power of a natural number
_**_ : ℚ → ℕ → ℚ
p ** ℕ.zero = 1ℚ
p ** (ℕ.suc n) = p · (p ** n)

-- NonZero ℚ to the power of any integer
_^_ : (p : ℚ) → (exp : ℤ) → {{nz : NonZero p}} → ℚ
p ^ (pos n) = p ** n
(p ^ negsuc ℕ.zero) ⦃ nz ⦄ = 1/ p
(p ^ negsuc (ℕ.suc n)) ⦃ nz ⦄ = (1/ p) · (p ^ negsuc n)

-------------------------------------------------
-- Properties of Min and Max

minIdem : ∀ (m : ℚ) → min m m ≡ m
minIdem m with ≤Dec m m
... | yes p = refl
... | no ¬p = refl

minComm : ∀ m n → min m n ≡ min n m
minComm m n with ≤Dec m n | ≤Dec n m
... | yes p | yes q = isAntisym≤ {m}{n} p q
... | yes p | no ¬q = refl
... | no ¬p | yes q = refl
... | no ¬p | no ¬q = ⊥.elim {A = λ x → n ≡ m}
  (n⋖m→¬m⋖n {m}{n} (<→⋖ (¬m≤n→n<m {n}{m} ¬q)) (<→⋖ (¬m≤n→n<m {m}{n} ¬p)))

minAssoc : ∀ m n o → min m (min n o) ≡ min (min m n) o
minAssoc m n o with ≤Dec m n | ≤Dec n o | ≤Dec m n
... | yes p | yes q | w = {!!}
  where
    step : min n o ≡ n
    step = p⊓q-def1 q
    step2 : min m n ≡ m
    step2 = p⊓q-def1 p
    step4 : m ≤ min n o
    step4 = subst {!!} step {!!}
    step3 : min m (min n o) ≡ m
    step3 = p⊓q-def1 step4
    step5 : min m n ≤ o
    step5 = {!!}
... | yes p | no ¬q | w = {!!}
... | no ¬p | v | w = {!!}



-------------------------------------------------
-- Properties of _**_ and _^_

p**0≡1 : ∀ p → 1ℚ ≡ p ** zero
p**0≡1 p = refl

0**0≡1 : 1ℚ ≡ 0ℚ ** zero
0**0≡1 = refl

p**x+y≡p**x·p**y : ∀ p x y → p ** (x ℕ.+ y) ≡ (p ** x) · (p ** y)
p**x+y≡p**x·p**y p zero y = sym (·IdL (p ** y))
p**x+y≡p**x·p**y p (suc x) y = cong (λ u → p · u) (p**x+y≡p**x·p**y p x y) ∙
 ·Assoc p (p ** x) (p ** y)

a**x·b**x≡ab**x : ∀ p q x → (p ** x) · (q ** x) ≡ (p · q) ** x
a**x·b**x≡ab**x p q zero = refl
a**x·b**x≡ab**x p q (suc x) =
  sym (ab'cd≡ac'bd p q (p ** x) (q ** x)) ∙
  cong (λ u → (p · q) · u) (a**x·b**x≡ab**x p q x)

p^0≡1 : ∀ p → {{nz : NonZero p}} → p ^ (pos zero) ≡ 1ℚ
p^0≡1 p {{nz}} = refl

p^pos≡p**n : ∀ p {z}{n} → z ≡ pos n → {{nz : NonZero p}} → p ^ z ≡ p ** n
p^pos≡p**n p z@{pos n'} {n} z≡n ⦃ nz ⦄ = cong (λ u → p ** u) (ℤ.injPos z≡n)
p^pos≡p**n p z@{negsuc n'} {n} z≡n ⦃ nz ⦄ =
  ⊥.elim {A = λ x → p ^ z ≡ p ** n} (ℤ.negsucNotpos n' n z≡n)

p^negsuc≡p**n : ∀ p {z}{n} → z ≡ negsuc n → {{nz : NonZero p}} →
  p ^ z ≡ (1/ p) ** (suc n)
p^negsuc≡p**n p z@{pos m} {n} z≡n ⦃ nz ⦄ =
  ⊥.elim {A = λ x → p ^ z ≡ (1/ p) ** (suc n)} (ℤ.posNotnegsuc m n z≡n)
p^negsuc≡p**n p {z@(negsuc zero)} {zero} z≡n ⦃ nz ⦄ = sym (·IdR (1/ p))
p^negsuc≡p**n p {z@(negsuc zero)} {suc n} z≡n ⦃ nz ⦄ =
  ⊥.elim {A = λ x → 1/ p ≡ 1/ p · (1/ p · (1/ p) ** n)}
   (znots (ℤ.injNegsuc z≡n))
p^negsuc≡p**n p {z@(negsuc (suc m))} {zero} z≡n ⦃ nz ⦄ =
  ⊥.elim {A = λ x → 1/ p · p ^ negsuc m ≡ 1/ p · 1ℚ}
   (znots (ℤ.injNegsuc (sym z≡n)))
p^negsuc≡p**n p {z@(negsuc (suc m))} {suc n} z≡n ⦃ nz ⦄ =
  cong (λ u → (1/ p) · u) step2

  where
    step : p ^ negsuc m ≡ (1/ p) ** suc n
    step = p^negsuc≡p**n p {!!} {{nz}}
    step1 : suc m ≡ suc n
    step1 = (ℤ.injNegsuc z≡n)
    step2 : p ^ negsuc m ≡ (1/ p) ** suc n
    step2 = p^negsuc≡p**n p {!!} --p^negsuc≡p**n p ?  --{!p!} {!!}

---------------

p^pos+y : ∀ p n y {{np : NonZero p}} → p ^ (pos n ℤ.+ y) ≡ (p ** n) · (p ^ y)
p^pos+y p n (pos m) ⦃ np ⦄ = {!!}
p^pos+y p n (negsuc m) ⦃ np ⦄ = {!!}


helper : ∀ p y {{np : NonZero p}} → p ^ ((pos (suc zero)) ℤ.+ y) ≡ p · (p ^ y)
helper p (pos zero) ⦃ np ⦄ = refl
helper p (pos (suc n)) ⦃ np ⦄ = {!!}
helper p (negsuc zero) ⦃ np ⦄ = {!!}
helper p (negsuc (suc n)) ⦃ np ⦄ = {!!}

p^x+y≡p^x·p^y : ∀ p x y {{np : NonZero p}} → p ^ (x ℤ.+ y) ≡ (p ^ x) · (p ^ y)
p^x+y≡p^x·p^y p (pos zero) y ⦃ np ⦄ = {!!}
p^x+y≡p^x·p^y p (pos (suc n)) y ⦃ np ⦄ = {!!} -- helper p n y
  where
    step : p ^ (pos n ℤ.+ y) ≡ (p ^ pos n) · (p ^ y)
    step = p^x+y≡p^x·p^y p (pos n) y {{np}}
    step2 : p ^ (pos (suc zero) ℤ.+ (pos n ℤ.+ y)) ≡ p · (p ^ (pos n ℤ.+ y))
    step2 = helper p (pos n ℤ.+ y)
    step3 : p ^ (pos n ℤ.+ y) ≡ (p ** n · p ^ y)
    step3 = {!!}


--p^x+y≡p^x·p^y p (pos n) (negsuc m) ⦃ np ⦄ = {!!}
p^x+y≡p^x·p^y p (negsuc n) y ⦃ np ⦄ = {!!}
--p^x+y≡p^x·p^y p (negsuc n) (negsuc m) ⦃ np ⦄ = {!!}


{-
p^x·q^x≡pq^x : ∀ p q x {{nz : NonZero p}} {{nz' : NonZero q}} →
  let ·nz = nonZero·nonZero≡nonZero p q in
  (p ^ x) · (q ^ x) ≡ (_^_) (p · q) x {{·nz}}
p^x·q^x≡pq^x p q x = {!!} --{{nz}} {{nz'}} = ?
-}
