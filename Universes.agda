{-# OPTIONS --without-K --safe #-}

module Universes where

open import Agda.Primitive public
 renaming (
            Level to Universe 
          ; lzero to ð¤â       
          ; lsuc to _âº        
          ; SetÏ to ð¤Ï        
          )
 using    (_â_)  

Type = Î» â â Set â

_Ì   : (ð¤ : Universe) â Type (ð¤ âº)

ð¤âÌ  = Type ð¤

ð¤â = ð¤â âº
ð¤â = ð¤â âº
ð¤â = ð¤â âº

_âºâº : Universe â Universe
ð¤ âºâº = ð¤ âº âº

universe-of : {ð¤ : Universe} (X : ð¤âÌ ) â Universe
universe-of {ð¤} X = ð¤

infix  1 _Ì
