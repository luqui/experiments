{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving #-}

data Switch b a where
    SwitchA :: Switch b A
    SwitchB :: b -> Switch b B

class Switchable c where
    switch :: c -> Switch b c

data A = A

instance Switchable A where
    switch A = SwitchA 

newtype B = B A
    deriving (Switchable)

unSwitchB :: Switch b B -> b
unSwitchB (SwitchB y) = y

inconsistent :: b
inconsistent = unSwitchB (switch (B A))
