{-# OPTIONS --without-K #-}

-- Subscription status display.
-- CSS classes: .agdelte-sub, .agdelte-sub__status, .agdelte-sub__date

module Agdelte.Html.Controls.Subscription where

open import Data.String using (String; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)

open import Agdelte.Reactive.Node
open import Agdelte.Storage.AppStore using
  ( SubscriptionRecord; sbStatus; sbEndDate; sbAutoRenew
  ; SubStatus; SubActive; SubCancelled; SubPending; SubExpired
  )
open import Agdelte.I18n using (Locale; Ru; En; formatDate)

------------------------------------------------------------------------
-- Status labels
------------------------------------------------------------------------

subStatusLabel : Locale → SubStatus → String
subStatusLabel Ru SubPending   = "Ожидает оплаты"
subStatusLabel Ru SubActive    = "Подписка активна"
subStatusLabel Ru SubCancelled = "Подписка отменена"
subStatusLabel Ru SubExpired   = "Подписка истекла"
subStatusLabel En SubPending   = "Awaiting payment"
subStatusLabel En SubActive    = "Subscription active"
subStatusLabel En SubCancelled = "Subscription cancelled"
subStatusLabel En SubExpired   = "Subscription expired"

------------------------------------------------------------------------
-- Subscription status view
------------------------------------------------------------------------

-- | Show subscription status with end date.
-- For SubCancelled: "Подписка отменена — активна до DD.MM.YYYY"
-- For SubActive:    "Подписка активна до DD.MM.YYYY"
subscriptionStatusView : ∀ {M A}
                       → Locale
                       → (M → Maybe SubscriptionRecord)
                       → Node M A
subscriptionStatusView locale getSub =
  div (class "agdelte-sub" ∷ [])
    ( bindF render ∷ [])
  where
    render : _ → String
    render m with getSub m
    ... | nothing  = ""
    ... | just sub = renderSub sub

    untilLabel : String
    untilLabel with locale
    ... | Ru = " до "
    ... | En = " until "

    activeUntilLabel : String
    activeUntilLabel with locale
    ... | Ru = " — активна до "
    ... | En = " — active until "

    renderSub : SubscriptionRecord → String
    renderSub sub with sbStatus sub
    ... | SubPending   = subStatusLabel locale SubPending
    ... | SubExpired   = subStatusLabel locale SubExpired
    ... | SubActive    = subStatusLabel locale SubActive
                       ++ untilLabel ++ formatDate locale (sbEndDate sub)
    ... | SubCancelled = subStatusLabel locale SubCancelled
                       ++ activeUntilLabel ++ formatDate locale (sbEndDate sub)
