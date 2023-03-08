##### 1. Evaluate the following expressions
<pre>
  a. tt && (ff xor ˜ ff)
    True

  b. ˜ tt && (ff imp ff)
    False

  c. if tt xor tt then ff else ff
    False
</pre>

##### 2. What is the type of each of the following
<pre>
  a. tt
    Bool

  b. if tt then ff else tt
    Bool

  c. _∧_
    Bool → Bool → Bool

  d. Bool
    Set
</pre>

##### 3. Redefine some function in Bool
```agda
module Exercise.Chapter1 where

open import Definition.Bool hiding (_nand_)

_nand_ : Bool → Bool → Bool
a nand b = ¬ (a ∧ b)
```

##### 4. Define a datatype day which is similar to the B datatype, but has one 
constructor for each day of the week.
```agda
data Day : Set where
  Monday Tuesday Wednesday Thursday Friday Saturday Sunday : Day
```

##### 5. Using the day datatype from the previous problem, define a function 
nextday of type day -\> day, which given a day of the week will return the next
day of the week (so nextday Sunday should return Monday).
```agda
nextday : Day → Day
nextday Monday = Tuesday
nextday Tuesday = Wednesday
nextday Wednesday = Thursday
nextday Thursday = Friday
nextday Friday = Saturday
nextday Saturday = Sunday
nextday Sunday = Monday
```

##### 6. Define a datatype suit for suits from a standard deck of cards. You should
have one constructor for each of the four suits: hearts, spades, diamonds,
and clubs.
```agda
data Suit : Set where
  hearts spades diamonds clubs : Suit
```

##### 7. Define a function is-red which takes in a suit as defined in the previous
problem, and returns tt iff the suit is a red one (hearts and diamonds).
```agda
is-red : Suit → Bool
is-red hearts = True
is-red spades = False
is-red diamonds = True
is-red clubs = False
```