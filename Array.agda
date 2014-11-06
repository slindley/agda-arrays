module Array where

{- Agda gunk -}

-- equality data type
data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
infix 1 _==_
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

-- substitution principle
subst :  forall {k l}{X : Set k}{s t : X} ->
         s == t -> (P : X -> Set l) -> P s -> P t
subst refl P p = p

-- congruence
cong : forall {k l}{X : Set k}{Y : Set l}(f : X -> Y){x y} -> x == y -> f x == f y
cong f refl = refl

-- natural numbers
data Nat : Set where
  zero  :         Nat
  suc   : Nat ->  Nat
{-# BUILTIN NATURAL Nat #-}

-- bounded natural numbers
data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc  : {n : Nat} -> Fin n -> Fin (suc n)

-- arithmetic on naturals
_+Nat_ : Nat -> Nat -> Nat
zero +Nat y = y
suc x +Nat y = suc (x +Nat y)

_*Nat_ : Nat -> Nat -> Nat
zero *Nat y = zero
suc x *Nat y = y +Nat (x *Nat y)

-- forget bound
fog : forall {n} -> Fin n -> Nat
fog zero    = zero
fog (suc i) = suc (fog i)

-- introduce bound
bound : (n : Nat) -> Fin (suc n)
bound zero    = zero
bound (suc n) = suc (bound n)

bound-gap : {m : Nat} -> (n : Nat) -> Fin (suc n +Nat m)
bound-gap zero    = zero
bound-gap {m} (suc n) = suc (bound-gap {m} n)

-- weaken bound
wk : forall {m} -> Fin m -> Fin (suc m)
wk zero = zero
wk (suc i) = suc (wk i)

-- arithmetic on bounded naturals
_+Fin_ : forall {m n} -> Fin (suc m) -> Fin (suc n) -> Fin (suc (m +Nat n))
_+Fin_ {zero}  zero     j = j
_+Fin_ {suc m} zero     j = wk (_+Fin_{m} zero j)
_+Fin_ {zero}  (suc ()) j
_+Fin_ {suc m} (suc i)  j = suc (i +Fin j)

_*Fin_ : forall {m n} -> Fin (suc m) -> Fin (suc n) -> Fin (suc (m *Nat n))
zero *Fin j = zero
_*Fin_ {zero} (suc ()) j
_*Fin_ {suc m} (suc i) j = j +Fin (i *Fin j)


-- arrays as maps from naturals
Array : Set -> Nat -> Set
Array X n = Fin n -> X

map : forall {X Y n} -> (X -> Y) -> Array X n -> Array Y n
map f xs i = f (xs i)

fold : {X Y : Set} {n : Nat} -> (X -> Y -> Y) -> Y -> Array X n -> Y
fold {X} {Y} {zero} f y xs  = y
fold {X} {Y} {suc n} f y xs = f (xs zero) (fold {n = n}f y (\i -> xs (suc i)))

split : forall {X m n} -> Array X (m *Nat n) -> Array (Array X n) m
split {X}{zero} _ () _
split {X}{m}{zero} _ _ ()
split {X}{suc m}{suc n} xs i j = xs (j +Fin (i *Fin (bound (suc n))))

-- arithmetic lemmas
add-suc : (m n : Nat) -> m +Nat suc n == suc (m +Nat n)
add-suc zero n = refl
add-suc (suc m) n rewrite add-suc m n = refl

add-zero : (m : Nat) -> m +Nat zero == m
add-zero zero = refl
add-zero (suc m) rewrite add-zero m = refl

mul-zero : (m : Nat) -> m *Nat zero == zero
mul-zero zero = refl
mul-zero (suc m) rewrite mul-zero m = refl

{- Computing rows and columns from a one dimensional index -}

row' : (m n r x : Nat) -> Fin (x +Nat (suc m *Nat suc n)) -> Fin (suc m +Nat r)
row' zero    n r x       i       = bound r
row' m       n r (suc x) (suc i) = row' m n r x i
row' (suc m) n r (suc x) zero    = suc (row' m n r (suc x) zero)
row' (suc m) n r zero    i       = subst (add-suc (suc m) r) Fin (row' m n (suc r) (suc n) i)

row : forall {m n} -> Fin (m *Nat n) -> Fin m
row {zero} ()
row {suc m} {zero} i = wk (row{m}{zero} i)
row {suc m}{suc n} i = subst (add-zero (suc m)) Fin (row' m n zero zero i)

-- compute the column from a one-dimensional index
col' : (m n x : Nat) -> Fin (suc n) -> Fin (x +Nat (suc m *Nat suc n)) -> Fin (suc n)
col' m       n zero    (suc c) i       = zero  -- impossible
col' m       n (suc x) zero    i       = zero  -- impossible
col' m       n zero    zero    zero    = zero
col' m       n (suc x) (suc c) zero    = suc c
col' m       n (suc x) (suc c) (suc i) = col' m n x (wk c) i
col' zero    n zero    zero    (suc i) = suc (subst (add-zero n) Fin i)
col' (suc m) n zero    zero    (suc i) = col' m n n (bound n) i

col : forall {m n} -> Fin (m *Nat n) -> Fin n
col {zero} () 
col {m}{zero} i rewrite mul-zero m = i
col {suc m}{suc n} i = col' m n zero zero i

{- we can be a bit tighter if we want... -}

{-
pred : Nat -> Nat
pred zero = zero
pred (suc n) = n

--lemmas about forgetting bounds
fog-bound : (n : Nat) -> n == fog(bound n)
fog-bound zero    = refl
fog-bound (suc n) = cong suc (fog-bound n)

fog-wk : {n : Nat} -> (c : Fin n) -> fog c == fog (wk c)
fog-wk zero = refl
fog-wk (suc c) rewrite fog-wk {_} c = refl

-- the third argument is necessary in order to prove termination
-- the fifth argument allows us to dispense with the impossible cases
col'' : (m n x : Nat) -> (c : Fin (suc n)) -> (x == fog c) -> Fin (x +Nat (suc m *Nat suc n)) -> Fin (suc n)
col'' m       n zero    (suc c) () i
col'' m       n (suc x) zero    () i
col'' m       n zero    zero    p  zero    = zero
col'' m       n (suc x) (suc c) p  zero    = suc c
col'' m       n (suc x) (suc c) p  (suc i) = col'' m n x (wk c) (subst (fog-wk c) (\c -> x == c) (cong pred p)) i
col'' zero    n zero    zero    p  (suc i) = suc (subst (add-zero n) Fin i)
col'' (suc m) n zero    zero    p  (suc i) = col'' m n n (bound n) (fog-bound n) i

col : forall {m n} -> Fin (m *Nat n) -> Fin n
col {zero} () 
col {m}{zero} i rewrite mul-zero m = i
col {suc m}{suc n} i = col'' m n zero zero refl i
-}

join : forall {X m n} -> Array (Array X n) m -> Array X (m *Nat n)
join {m = m} xs i = xs (row i) (col{m} i) 

-- apply a Nat -> Nat function n times
pow : (Nat -> Nat) -> Nat -> (Nat -> Nat)
pow f zero    x = x
pow f (suc n) x = f (pow f n x)

-- induction principle for pow
f-pow : (f : Nat -> Nat) -> (m n : Nat) -> f (pow f n m) == pow f n (f m)
f-pow f m zero = refl
f-pow f m (suc n) rewrite f-pow f m n = refl

iterate : {m : Nat} -> {f : Nat -> Nat} -> forall {X} -> (n : Nat) ->
            ((p : Nat) -> Array X p -> Array X (f p)) -> Array X m ->
               Array X ((pow f) n m)
iterate zero h xs = xs   
iterate {m} {f} (suc n) h xs rewrite f-pow f m n = iterate {f m} {f} n h (h m xs)


-- converting arrays to lists
tail : forall {X n} -> Array X (suc n) -> Array X n
tail xs i = xs (suc i)

data List (X : Set) : Set where
  <>    :                 List X
  _,_   : X -> List X ->  List X
infixr 4 _,_

array-to-list : forall {n X} -> Array X n -> List X
array-to-list {zero}  xs = <>
array-to-list {suc n} xs = xs zero , array-to-list {n} (tail xs)


-- tests
xs : Array Nat 4
xs x = fog (suc x) *Nat 2

f1 : Nat -> Nat
f1 x = suc x

h1 : (p : Nat) -> Array Nat p -> Array Nat (f1 p)
h1 p xs zero = 42
h1 p xs (suc i) = xs i

test1 = array-to-list (iterate 2 h1 xs)

f2 : Nat -> Nat
f2 x = x *Nat 2

h2 : (p : Nat) -> Array Nat p -> Array Nat (f2 p)
h2 p xs i = xs (row i) +Nat (fog i)

test2 = array-to-list (iterate 3 h2 xs)


