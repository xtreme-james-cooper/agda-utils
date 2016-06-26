module AgdaUtils.Function where

open import AgdaUtils.Basics

update : {A B : Set} -> equality A -> (A -> B) -> A -> B -> A -> B
update aeq f a b a' with aeq a a' 
update aeq f a b a' | Yes _ = b
update aeq f a b a' | No _  = f a'
