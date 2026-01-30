{-# OPTIONS --without-K #-}

-- Html Events: DOM event handlers

module Agdelte.Html.Events where

open import Data.String using (String)

open import Agdelte.Html.Types

private
  variable
    Msg : Set

------------------------------------------------------------------------
-- Mouse events
------------------------------------------------------------------------

onClick : Msg → Attr Msg
onClick = on "click"

-- onClick with preventDefault (for navigation links)
onClickPrevent : Msg → Attr Msg
onClickPrevent = onPrevent "click"

onDoubleClick : Msg → Attr Msg
onDoubleClick = on "dblclick"

onMouseDown : Msg → Attr Msg
onMouseDown = on "mousedown"

onMouseUp : Msg → Attr Msg
onMouseUp = on "mouseup"

onMouseEnter : Msg → Attr Msg
onMouseEnter = on "mouseenter"

onMouseLeave : Msg → Attr Msg
onMouseLeave = on "mouseleave"

onMouseOver : Msg → Attr Msg
onMouseOver = on "mouseover"

onMouseOut : Msg → Attr Msg
onMouseOut = on "mouseout"

onMouseMove : Msg → Attr Msg
onMouseMove = on "mousemove"

onContextMenu : Msg → Attr Msg
onContextMenu = on "contextmenu"

------------------------------------------------------------------------
-- Keyboard events
------------------------------------------------------------------------

onKeyDown : (String → Msg) → Attr Msg
onKeyDown = onKey "keydown"

onKeyUp : (String → Msg) → Attr Msg
onKeyUp = onKey "keyup"

onKeyPress : (String → Msg) → Attr Msg
onKeyPress = onKey "keypress"

-- Special keys
onEnter : Msg → Attr Msg
onEnter msg = onKey "keydown" (λ key → msg)  -- Filtered at runtime

onEscape : Msg → Attr Msg
onEscape msg = onKey "keydown" (λ key → msg)

------------------------------------------------------------------------
-- Form events
------------------------------------------------------------------------

onInput' : (String → Msg) → Attr Msg
onInput' = onInput

onChange : Msg → Attr Msg
onChange = on "change"

onSubmit : Msg → Attr Msg
onSubmit = on "submit"

onReset : Msg → Attr Msg
onReset = on "reset"

onFocus : Msg → Attr Msg
onFocus = on "focus"

onBlur : Msg → Attr Msg
onBlur = on "blur"

onSelect : Msg → Attr Msg
onSelect = on "select"

------------------------------------------------------------------------
-- Focus events
------------------------------------------------------------------------

onFocusIn : Msg → Attr Msg
onFocusIn = on "focusin"

onFocusOut : Msg → Attr Msg
onFocusOut = on "focusout"

------------------------------------------------------------------------
-- Drag events
------------------------------------------------------------------------

onDrag : Msg → Attr Msg
onDrag = on "drag"

onDragStart : Msg → Attr Msg
onDragStart = on "dragstart"

onDragEnd : Msg → Attr Msg
onDragEnd = on "dragend"

onDragEnter : Msg → Attr Msg
onDragEnter = on "dragenter"

onDragLeave : Msg → Attr Msg
onDragLeave = on "dragleave"

onDragOver : Msg → Attr Msg
onDragOver = on "dragover"

onDrop : Msg → Attr Msg
onDrop = on "drop"

------------------------------------------------------------------------
-- Touch events
------------------------------------------------------------------------

onTouchStart : Msg → Attr Msg
onTouchStart = on "touchstart"

onTouchEnd : Msg → Attr Msg
onTouchEnd = on "touchend"

onTouchMove : Msg → Attr Msg
onTouchMove = on "touchmove"

onTouchCancel : Msg → Attr Msg
onTouchCancel = on "touchcancel"

------------------------------------------------------------------------
-- Scroll events
------------------------------------------------------------------------

onScroll : Msg → Attr Msg
onScroll = on "scroll"

onWheel : Msg → Attr Msg
onWheel = on "wheel"

------------------------------------------------------------------------
-- Media events
------------------------------------------------------------------------

onPlay : Msg → Attr Msg
onPlay = on "play"

onPause : Msg → Attr Msg
onPause = on "pause"

onEnded : Msg → Attr Msg
onEnded = on "ended"

onTimeUpdate : Msg → Attr Msg
onTimeUpdate = on "timeupdate"

onVolumeChange : Msg → Attr Msg
onVolumeChange = on "volumechange"

onLoadedData : Msg → Attr Msg
onLoadedData = on "loadeddata"

onLoadedMetadata : Msg → Attr Msg
onLoadedMetadata = on "loadedmetadata"

onCanPlay : Msg → Attr Msg
onCanPlay = on "canplay"

onError : Msg → Attr Msg
onError = on "error"

------------------------------------------------------------------------
-- Animation events
------------------------------------------------------------------------

onAnimationStart : Msg → Attr Msg
onAnimationStart = on "animationstart"

onAnimationEnd : Msg → Attr Msg
onAnimationEnd = on "animationend"

onAnimationIteration : Msg → Attr Msg
onAnimationIteration = on "animationiteration"

onTransitionEnd : Msg → Attr Msg
onTransitionEnd = on "transitionend"

------------------------------------------------------------------------
-- Clipboard events
------------------------------------------------------------------------

onCopy : Msg → Attr Msg
onCopy = on "copy"

onCut : Msg → Attr Msg
onCut = on "cut"

onPaste : Msg → Attr Msg
onPaste = on "paste"

------------------------------------------------------------------------
-- Utility: prevent default and stop propagation
------------------------------------------------------------------------

onSubmitPrevent : Msg → Attr Msg
onSubmitPrevent = onPrevent "submit"
