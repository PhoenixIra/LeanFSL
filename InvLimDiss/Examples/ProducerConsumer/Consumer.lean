import InvLimDiss.Examples.ProducerConsumer.Basic

open Syntax CFSL FSL SL

theorem consumer_sound (y : ℕ) :
    ⊢ [[rInv y]]
    ⦃⁅is_in_ico "y3" (-1) y⁆ ⊓ var "l" === sub (dec $ const y) (var "y3")⦄
  consumer
  ⦃ var "l" === const ↑y ⦄ := sorry
