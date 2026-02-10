{-# OPTIONS --without-K #-}

-- SVG Icon Library
-- Common SVG icons for UI components

module Agdelte.Svg.Controls.Icons where

open import Data.String using (String; _++_)
open import Data.Float using (Float)
open import Data.List using (List; []; _∷_)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr)
open import Agdelte.Svg.Elements using (svg; g; path'; circle'; line'; rect'; polyline')
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Icon wrapper
------------------------------------------------------------------------

-- | Base icon wrapper with consistent sizing
icon : ∀ {M A} → Float → Float → String → List (Node M A) → Node M A
icon w h className children =
  svg ( widthF w ∷ heightF h
      ∷ viewBox_ "0 0 24 24"
      ∷ fill_ "none"
      ∷ stroke_ "currentColor"
      ∷ attr "stroke-width" "2"
      ∷ attr "stroke-linecap" "round"
      ∷ attr "stroke-linejoin" "round"
      ∷ attr "class" ("agdelte-icon " ++ className)
      ∷ [] )
    children

-- | Default 24x24 icon
icon24 : ∀ {M A} → String → List (Node M A) → Node M A
icon24 = icon 24.0 24.0

-- | Small 16x16 icon
icon16 : ∀ {M A} → String → List (Node M A) → Node M A
icon16 = icon 16.0 16.0

-- | Large 32x32 icon
icon32 : ∀ {M A} → String → List (Node M A) → Node M A
icon32 = icon 32.0 32.0

------------------------------------------------------------------------
-- Navigation Icons
------------------------------------------------------------------------

-- | Chevron left <
iconChevronLeft : ∀ {M A} → Float → Node M A
iconChevronLeft size =
  icon size size "icon-chevron-left"
    ( polyline' ( attr "points" "15 18 9 12 15 6" ∷ [] ) []
    ∷ [] )

-- | Chevron right >
iconChevronRight : ∀ {M A} → Float → Node M A
iconChevronRight size =
  icon size size "icon-chevron-right"
    ( polyline' ( attr "points" "9 18 15 12 9 6" ∷ [] ) []
    ∷ [] )

-- | Chevron up ^
iconChevronUp : ∀ {M A} → Float → Node M A
iconChevronUp size =
  icon size size "icon-chevron-up"
    ( polyline' ( attr "points" "18 15 12 9 6 15" ∷ [] ) []
    ∷ [] )

-- | Chevron down v
iconChevronDown : ∀ {M A} → Float → Node M A
iconChevronDown size =
  icon size size "icon-chevron-down"
    ( polyline' ( attr "points" "6 9 12 15 18 9" ∷ [] ) []
    ∷ [] )

-- | Arrow left ←
iconArrowLeft : ∀ {M A} → Float → Node M A
iconArrowLeft size =
  icon size size "icon-arrow-left"
    ( line' ( x1_ "19" ∷ y1_ "12" ∷ x2_ "5" ∷ y2_ "12" ∷ [] ) []
    ∷ polyline' ( attr "points" "12 19 5 12 12 5" ∷ [] ) []
    ∷ [] )

-- | Arrow right →
iconArrowRight : ∀ {M A} → Float → Node M A
iconArrowRight size =
  icon size size "icon-arrow-right"
    ( line' ( x1_ "5" ∷ y1_ "12" ∷ x2_ "19" ∷ y2_ "12" ∷ [] ) []
    ∷ polyline' ( attr "points" "12 5 19 12 12 19" ∷ [] ) []
    ∷ [] )

-- | Arrow up ↑
iconArrowUp : ∀ {M A} → Float → Node M A
iconArrowUp size =
  icon size size "icon-arrow-up"
    ( line' ( x1_ "12" ∷ y1_ "19" ∷ x2_ "12" ∷ y2_ "5" ∷ [] ) []
    ∷ polyline' ( attr "points" "5 12 12 5 19 12" ∷ [] ) []
    ∷ [] )

-- | Arrow down ↓
iconArrowDown : ∀ {M A} → Float → Node M A
iconArrowDown size =
  icon size size "icon-arrow-down"
    ( line' ( x1_ "12" ∷ y1_ "5" ∷ x2_ "12" ∷ y2_ "19" ∷ [] ) []
    ∷ polyline' ( attr "points" "19 12 12 19 5 12" ∷ [] ) []
    ∷ [] )

-- | Home 🏠
iconHome : ∀ {M A} → Float → Node M A
iconHome size =
  icon size size "icon-home"
    ( path' ( d_ "M3 9l9-7 9 7v11a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2z" ∷ [] ) []
    ∷ polyline' ( attr "points" "9 22 9 12 15 12 15 22" ∷ [] ) []
    ∷ [] )

-- | Menu (hamburger) ☰
iconMenu : ∀ {M A} → Float → Node M A
iconMenu size =
  icon size size "icon-menu"
    ( line' ( x1_ "3" ∷ y1_ "12" ∷ x2_ "21" ∷ y2_ "12" ∷ [] ) []
    ∷ line' ( x1_ "3" ∷ y1_ "6" ∷ x2_ "21" ∷ y2_ "6" ∷ [] ) []
    ∷ line' ( x1_ "3" ∷ y1_ "18" ∷ x2_ "21" ∷ y2_ "18" ∷ [] ) []
    ∷ [] )

-- | More vertical (kebab) ⋮
iconMoreVertical : ∀ {M A} → Float → Node M A
iconMoreVertical size =
  icon size size "icon-more-vertical"
    ( circle' ( cxF 12.0 ∷ cyF 12.0 ∷ rF 1.0 ∷ [] ) []
    ∷ circle' ( cxF 12.0 ∷ cyF 5.0 ∷ rF 1.0 ∷ [] ) []
    ∷ circle' ( cxF 12.0 ∷ cyF 19.0 ∷ rF 1.0 ∷ [] ) []
    ∷ [] )

-- | More horizontal (meatballs) ⋯
iconMoreHorizontal : ∀ {M A} → Float → Node M A
iconMoreHorizontal size =
  icon size size "icon-more-horizontal"
    ( circle' ( cxF 12.0 ∷ cyF 12.0 ∷ rF 1.0 ∷ [] ) []
    ∷ circle' ( cxF 19.0 ∷ cyF 12.0 ∷ rF 1.0 ∷ [] ) []
    ∷ circle' ( cxF 5.0 ∷ cyF 12.0 ∷ rF 1.0 ∷ [] ) []
    ∷ [] )

------------------------------------------------------------------------
-- Action Icons
------------------------------------------------------------------------

-- | Close / X ✕
iconClose : ∀ {M A} → Float → Node M A
iconClose size =
  icon size size "icon-close"
    ( line' ( x1_ "18" ∷ y1_ "6" ∷ x2_ "6" ∷ y2_ "18" ∷ [] ) []
    ∷ line' ( x1_ "6" ∷ y1_ "6" ∷ x2_ "18" ∷ y2_ "18" ∷ [] ) []
    ∷ [] )

-- | Check / Tick ✓
iconCheck : ∀ {M A} → Float → Node M A
iconCheck size =
  icon size size "icon-check"
    ( polyline' ( attr "points" "20 6 9 17 4 12" ∷ [] ) []
    ∷ [] )

-- | Plus +
iconPlus : ∀ {M A} → Float → Node M A
iconPlus size =
  icon size size "icon-plus"
    ( line' ( x1_ "12" ∷ y1_ "5" ∷ x2_ "12" ∷ y2_ "19" ∷ [] ) []
    ∷ line' ( x1_ "5" ∷ y1_ "12" ∷ x2_ "19" ∷ y2_ "12" ∷ [] ) []
    ∷ [] )

-- | Minus −
iconMinus : ∀ {M A} → Float → Node M A
iconMinus size =
  icon size size "icon-minus"
    ( line' ( x1_ "5" ∷ y1_ "12" ∷ x2_ "19" ∷ y2_ "12" ∷ [] ) []
    ∷ [] )

-- | Search 🔍
iconSearch : ∀ {M A} → Float → Node M A
iconSearch size =
  icon size size "icon-search"
    ( circle' ( cxF 11.0 ∷ cyF 11.0 ∷ rF 8.0 ∷ [] ) []
    ∷ line' ( x1_ "21" ∷ y1_ "21" ∷ x2_ "16.65" ∷ y2_ "16.65" ∷ [] ) []
    ∷ [] )

-- | Edit (pencil) ✏️
iconEdit : ∀ {M A} → Float → Node M A
iconEdit size =
  icon size size "icon-edit"
    ( path' ( d_ "M11 4H4a2 2 0 0 0-2 2v14a2 2 0 0 0 2 2h14a2 2 0 0 0 2-2v-7" ∷ [] ) []
    ∷ path' ( d_ "M18.5 2.5a2.121 2.121 0 0 1 3 3L12 15l-4 1 1-4 9.5-9.5z" ∷ [] ) []
    ∷ [] )

-- | Trash / Delete 🗑️
iconTrash : ∀ {M A} → Float → Node M A
iconTrash size =
  icon size size "icon-trash"
    ( polyline' ( attr "points" "3 6 5 6 21 6" ∷ [] ) []
    ∷ path' ( d_ "M19 6v14a2 2 0 0 1-2 2H7a2 2 0 0 1-2-2V6m3 0V4a2 2 0 0 1 2-2h4a2 2 0 0 1 2 2v2" ∷ [] ) []
    ∷ line' ( x1_ "10" ∷ y1_ "11" ∷ x2_ "10" ∷ y2_ "17" ∷ [] ) []
    ∷ line' ( x1_ "14" ∷ y1_ "11" ∷ x2_ "14" ∷ y2_ "17" ∷ [] ) []
    ∷ [] )

-- | Copy 📋
iconCopy : ∀ {M A} → Float → Node M A
iconCopy size =
  icon size size "icon-copy"
    ( rect' ( xF 9.0 ∷ yF 9.0 ∷ widthF 13.0 ∷ heightF 13.0 ∷ attr "rx" "2" ∷ attr "ry" "2" ∷ [] ) []
    ∷ path' ( d_ "M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1" ∷ [] ) []
    ∷ [] )

-- | Download ⬇️
iconDownload : ∀ {M A} → Float → Node M A
iconDownload size =
  icon size size "icon-download"
    ( path' ( d_ "M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4" ∷ [] ) []
    ∷ polyline' ( attr "points" "7 10 12 15 17 10" ∷ [] ) []
    ∷ line' ( x1_ "12" ∷ y1_ "15" ∷ x2_ "12" ∷ y2_ "3" ∷ [] ) []
    ∷ [] )

-- | Upload ⬆️
iconUpload : ∀ {M A} → Float → Node M A
iconUpload size =
  icon size size "icon-upload"
    ( path' ( d_ "M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4" ∷ [] ) []
    ∷ polyline' ( attr "points" "17 8 12 3 7 8" ∷ [] ) []
    ∷ line' ( x1_ "12" ∷ y1_ "3" ∷ x2_ "12" ∷ y2_ "15" ∷ [] ) []
    ∷ [] )

-- | Refresh ↻
iconRefresh : ∀ {M A} → Float → Node M A
iconRefresh size =
  icon size size "icon-refresh"
    ( polyline' ( attr "points" "23 4 23 10 17 10" ∷ [] ) []
    ∷ polyline' ( attr "points" "1 20 1 14 7 14" ∷ [] ) []
    ∷ path' ( d_ "M3.51 9a9 9 0 0 1 14.85-3.36L23 10M1 14l4.64 4.36A9 9 0 0 0 20.49 15" ∷ [] ) []
    ∷ [] )

-- | Settings ⚙️
iconSettings : ∀ {M A} → Float → Node M A
iconSettings size =
  icon size size "icon-settings"
    ( circle' ( cxF 12.0 ∷ cyF 12.0 ∷ rF 3.0 ∷ [] ) []
    ∷ path' ( d_ "M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 0 1 0 2.83 2 2 0 0 1-2.83 0l-.06-.06a1.65 1.65 0 0 0-1.82-.33 1.65 1.65 0 0 0-1 1.51V21a2 2 0 0 1-2 2 2 2 0 0 1-2-2v-.09A1.65 1.65 0 0 0 9 19.4a1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 0 1-2.83 0 2 2 0 0 1 0-2.83l.06-.06a1.65 1.65 0 0 0 .33-1.82 1.65 1.65 0 0 0-1.51-1H3a2 2 0 0 1-2-2 2 2 0 0 1 2-2h.09A1.65 1.65 0 0 0 4.6 9a1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 0 1 0-2.83 2 2 0 0 1 2.83 0l.06.06a1.65 1.65 0 0 0 1.82.33H9a1.65 1.65 0 0 0 1-1.51V3a2 2 0 0 1 2-2 2 2 0 0 1 2 2v.09a1.65 1.65 0 0 0 1 1.51 1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 0 1 2.83 0 2 2 0 0 1 0 2.83l-.06.06a1.65 1.65 0 0 0-.33 1.82V9a1.65 1.65 0 0 0 1.51 1H21a2 2 0 0 1 2 2 2 2 0 0 1-2 2h-.09a1.65 1.65 0 0 0-1.51 1z" ∷ [] ) []
    ∷ [] )

------------------------------------------------------------------------
-- File Icons
------------------------------------------------------------------------

-- | File 📄
iconFile : ∀ {M A} → Float → Node M A
iconFile size =
  icon size size "icon-file"
    ( path' ( d_ "M13 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V9z" ∷ [] ) []
    ∷ polyline' ( attr "points" "13 2 13 9 20 9" ∷ [] ) []
    ∷ [] )

-- | Folder 📁
iconFolder : ∀ {M A} → Float → Node M A
iconFolder size =
  icon size size "icon-folder"
    ( path' ( d_ "M22 19a2 2 0 0 1-2 2H4a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h5l2 3h9a2 2 0 0 1 2 2z" ∷ [] ) []
    ∷ [] )

-- | Image 🖼️
iconImage : ∀ {M A} → Float → Node M A
iconImage size =
  icon size size "icon-image"
    ( rect' ( xF 3.0 ∷ yF 3.0 ∷ widthF 18.0 ∷ heightF 18.0 ∷ attr "rx" "2" ∷ attr "ry" "2" ∷ [] ) []
    ∷ circle' ( cxF 8.5 ∷ cyF 8.5 ∷ rF 1.5 ∷ [] ) []
    ∷ polyline' ( attr "points" "21 15 16 10 5 21" ∷ [] ) []
    ∷ [] )

-- | Video 🎥
iconVideo : ∀ {M A} → Float → Node M A
iconVideo size =
  icon size size "icon-video"
    ( rect' ( xF 2.0 ∷ yF 6.0 ∷ widthF 14.0 ∷ heightF 12.0 ∷ attr "rx" "2" ∷ attr "ry" "2" ∷ [] ) []
    ∷ path' ( d_ "M22 8l-4 4 4 4V8z" ∷ [] ) []
    ∷ [] )

-- | Music 🎵
iconMusic : ∀ {M A} → Float → Node M A
iconMusic size =
  icon size size "icon-music"
    ( path' ( d_ "M9 18V5l12-2v13" ∷ [] ) []
    ∷ circle' ( cxF 6.0 ∷ cyF 18.0 ∷ rF 3.0 ∷ [] ) []
    ∷ circle' ( cxF 18.0 ∷ cyF 16.0 ∷ rF 3.0 ∷ [] ) []
    ∷ [] )

------------------------------------------------------------------------
-- Communication Icons
------------------------------------------------------------------------

-- | Mail ✉️
iconMail : ∀ {M A} → Float → Node M A
iconMail size =
  icon size size "icon-mail"
    ( path' ( d_ "M4 4h16c1.1 0 2 .9 2 2v12c0 1.1-.9 2-2 2H4c-1.1 0-2-.9-2-2V6c0-1.1.9-2 2-2z" ∷ [] ) []
    ∷ polyline' ( attr "points" "22,6 12,13 2,6" ∷ [] ) []
    ∷ [] )

-- | Phone 📞
iconPhone : ∀ {M A} → Float → Node M A
iconPhone size =
  icon size size "icon-phone"
    ( path' ( d_ "M22 16.92v3a2 2 0 0 1-2.18 2 19.79 19.79 0 0 1-8.63-3.07 19.5 19.5 0 0 1-6-6 19.79 19.79 0 0 1-3.07-8.67A2 2 0 0 1 4.11 2h3a2 2 0 0 1 2 1.72 12.84 12.84 0 0 0 .7 2.81 2 2 0 0 1-.45 2.11L8.09 9.91a16 16 0 0 0 6 6l1.27-1.27a2 2 0 0 1 2.11-.45 12.84 12.84 0 0 0 2.81.7A2 2 0 0 1 22 16.92z" ∷ [] ) []
    ∷ [] )

-- | Message bubble 💬
iconMessage : ∀ {M A} → Float → Node M A
iconMessage size =
  icon size size "icon-message"
    ( path' ( d_ "M21 15a2 2 0 0 1-2 2H7l-4 4V5a2 2 0 0 1 2-2h14a2 2 0 0 1 2 2z" ∷ [] ) []
    ∷ [] )

-- | Bell (notification) 🔔
iconBell : ∀ {M A} → Float → Node M A
iconBell size =
  icon size size "icon-bell"
    ( path' ( d_ "M18 8A6 6 0 0 0 6 8c0 7-3 9-3 9h18s-3-2-3-9" ∷ [] ) []
    ∷ path' ( d_ "M13.73 21a2 2 0 0 1-3.46 0" ∷ [] ) []
    ∷ [] )

------------------------------------------------------------------------
-- User Icons
------------------------------------------------------------------------

-- | User 👤
iconUser : ∀ {M A} → Float → Node M A
iconUser size =
  icon size size "icon-user"
    ( path' ( d_ "M20 21v-2a4 4 0 0 0-4-4H8a4 4 0 0 0-4 4v2" ∷ [] ) []
    ∷ circle' ( cxF 12.0 ∷ cyF 7.0 ∷ rF 4.0 ∷ [] ) []
    ∷ [] )

-- | Users 👥
iconUsers : ∀ {M A} → Float → Node M A
iconUsers size =
  icon size size "icon-users"
    ( path' ( d_ "M17 21v-2a4 4 0 0 0-4-4H5a4 4 0 0 0-4 4v2" ∷ [] ) []
    ∷ circle' ( cxF 9.0 ∷ cyF 7.0 ∷ rF 4.0 ∷ [] ) []
    ∷ path' ( d_ "M23 21v-2a4 4 0 0 0-3-3.87" ∷ [] ) []
    ∷ path' ( d_ "M16 3.13a4 4 0 0 1 0 7.75" ∷ [] ) []
    ∷ [] )

-- | User Plus (add user)
iconUserPlus : ∀ {M A} → Float → Node M A
iconUserPlus size =
  icon size size "icon-user-plus"
    ( path' ( d_ "M16 21v-2a4 4 0 0 0-4-4H5a4 4 0 0 0-4 4v2" ∷ [] ) []
    ∷ circle' ( cxF 8.5 ∷ cyF 7.0 ∷ rF 4.0 ∷ [] ) []
    ∷ line' ( x1_ "20" ∷ y1_ "8" ∷ x2_ "20" ∷ y2_ "14" ∷ [] ) []
    ∷ line' ( x1_ "23" ∷ y1_ "11" ∷ x2_ "17" ∷ y2_ "11" ∷ [] ) []
    ∷ [] )

------------------------------------------------------------------------
-- Status Icons
------------------------------------------------------------------------

-- | Info ℹ️
iconInfo : ∀ {M A} → Float → Node M A
iconInfo size =
  icon size size "icon-info"
    ( circle' ( cxF 12.0 ∷ cyF 12.0 ∷ rF 10.0 ∷ [] ) []
    ∷ line' ( x1_ "12" ∷ y1_ "16" ∷ x2_ "12" ∷ y2_ "12" ∷ [] ) []
    ∷ line' ( x1_ "12" ∷ y1_ "8" ∷ x2_ "12.01" ∷ y2_ "8" ∷ [] ) []
    ∷ [] )

-- | Warning ⚠️
iconWarning : ∀ {M A} → Float → Node M A
iconWarning size =
  icon size size "icon-warning"
    ( path' ( d_ "M10.29 3.86L1.82 18a2 2 0 0 0 1.71 3h16.94a2 2 0 0 0 1.71-3L13.71 3.86a2 2 0 0 0-3.42 0z" ∷ [] ) []
    ∷ line' ( x1_ "12" ∷ y1_ "9" ∷ x2_ "12" ∷ y2_ "13" ∷ [] ) []
    ∷ line' ( x1_ "12" ∷ y1_ "17" ∷ x2_ "12.01" ∷ y2_ "17" ∷ [] ) []
    ∷ [] )

-- | Error ❌
iconError : ∀ {M A} → Float → Node M A
iconError size =
  icon size size "icon-error"
    ( circle' ( cxF 12.0 ∷ cyF 12.0 ∷ rF 10.0 ∷ [] ) []
    ∷ line' ( x1_ "15" ∷ y1_ "9" ∷ x2_ "9" ∷ y2_ "15" ∷ [] ) []
    ∷ line' ( x1_ "9" ∷ y1_ "9" ∷ x2_ "15" ∷ y2_ "15" ∷ [] ) []
    ∷ [] )

-- | Success / Check circle ✅
iconSuccess : ∀ {M A} → Float → Node M A
iconSuccess size =
  icon size size "icon-success"
    ( path' ( d_ "M22 11.08V12a10 10 0 1 1-5.93-9.14" ∷ [] ) []
    ∷ polyline' ( attr "points" "22 4 12 14.01 9 11.01" ∷ [] ) []
    ∷ [] )

-- | Help / Question ❓
iconHelp : ∀ {M A} → Float → Node M A
iconHelp size =
  icon size size "icon-help"
    ( circle' ( cxF 12.0 ∷ cyF 12.0 ∷ rF 10.0 ∷ [] ) []
    ∷ path' ( d_ "M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3" ∷ [] ) []
    ∷ line' ( x1_ "12" ∷ y1_ "17" ∷ x2_ "12.01" ∷ y2_ "17" ∷ [] ) []
    ∷ [] )

------------------------------------------------------------------------
-- Media Controls
------------------------------------------------------------------------

-- | Play ▶️
iconPlay : ∀ {M A} → Float → Node M A
iconPlay size =
  icon size size "icon-play"
    ( path' ( d_ "M5 3l14 9-14 9V3z" ∷ fill_ "currentColor" ∷ [] ) []
    ∷ [] )

-- | Pause ⏸️
iconPause : ∀ {M A} → Float → Node M A
iconPause size =
  icon size size "icon-pause"
    ( rect' ( xF 6.0 ∷ yF 4.0 ∷ widthF 4.0 ∷ heightF 16.0 ∷ [] ) []
    ∷ rect' ( xF 14.0 ∷ yF 4.0 ∷ widthF 4.0 ∷ heightF 16.0 ∷ [] ) []
    ∷ [] )

-- | Stop ⏹️
iconStop : ∀ {M A} → Float → Node M A
iconStop size =
  icon size size "icon-stop"
    ( rect' ( xF 4.0 ∷ yF 4.0 ∷ widthF 16.0 ∷ heightF 16.0 ∷ fill_ "currentColor" ∷ [] ) []
    ∷ [] )

-- | Skip forward ⏭️
iconSkipForward : ∀ {M A} → Float → Node M A
iconSkipForward size =
  icon size size "icon-skip-forward"
    ( path' ( d_ "M5 4l10 8-10 8V4z" ∷ fill_ "currentColor" ∷ [] ) []
    ∷ line' ( x1_ "19" ∷ y1_ "5" ∷ x2_ "19" ∷ y2_ "19" ∷ [] ) []
    ∷ [] )

-- | Skip back ⏮️
iconSkipBack : ∀ {M A} → Float → Node M A
iconSkipBack size =
  icon size size "icon-skip-back"
    ( path' ( d_ "M19 20L9 12l10-8v16z" ∷ fill_ "currentColor" ∷ [] ) []
    ∷ line' ( x1_ "5" ∷ y1_ "19" ∷ x2_ "5" ∷ y2_ "5" ∷ [] ) []
    ∷ [] )

-- | Volume high 🔊
iconVolumeHigh : ∀ {M A} → Float → Node M A
iconVolumeHigh size =
  icon size size "icon-volume-high"
    ( path' ( d_ "M11 5L6 9H2v6h4l5 4V5z" ∷ [] ) []
    ∷ path' ( d_ "M19.07 4.93a10 10 0 0 1 0 14.14M15.54 8.46a5 5 0 0 1 0 7.07" ∷ [] ) []
    ∷ [] )

-- | Volume mute 🔇
iconVolumeMute : ∀ {M A} → Float → Node M A
iconVolumeMute size =
  icon size size "icon-volume-mute"
    ( path' ( d_ "M11 5L6 9H2v6h4l5 4V5z" ∷ [] ) []
    ∷ line' ( x1_ "23" ∷ y1_ "9" ∷ x2_ "17" ∷ y2_ "15" ∷ [] ) []
    ∷ line' ( x1_ "17" ∷ y1_ "9" ∷ x2_ "23" ∷ y2_ "15" ∷ [] ) []
    ∷ [] )

------------------------------------------------------------------------
-- Misc Icons
------------------------------------------------------------------------

-- | Star ⭐
iconStar : ∀ {M A} → Float → Node M A
iconStar size =
  icon size size "icon-star"
    ( path' ( d_ "M12 2l3.09 6.26L22 9.27l-5 4.87 1.18 6.88L12 17.77l-6.18 3.25L7 14.14 2 9.27l6.91-1.01L12 2z" ∷ [] ) []
    ∷ [] )

-- | Heart ❤️
iconHeart : ∀ {M A} → Float → Node M A
iconHeart size =
  icon size size "icon-heart"
    ( path' ( d_ "M20.84 4.61a5.5 5.5 0 0 0-7.78 0L12 5.67l-1.06-1.06a5.5 5.5 0 0 0-7.78 7.78l1.06 1.06L12 21.23l7.78-7.78 1.06-1.06a5.5 5.5 0 0 0 0-7.78z" ∷ [] ) []
    ∷ [] )

-- | Clock 🕐
iconClock : ∀ {M A} → Float → Node M A
iconClock size =
  icon size size "icon-clock"
    ( circle' ( cxF 12.0 ∷ cyF 12.0 ∷ rF 10.0 ∷ [] ) []
    ∷ polyline' ( attr "points" "12 6 12 12 16 14" ∷ [] ) []
    ∷ [] )

-- | Calendar 📅
iconCalendar : ∀ {M A} → Float → Node M A
iconCalendar size =
  icon size size "icon-calendar"
    ( rect' ( xF 3.0 ∷ yF 4.0 ∷ widthF 18.0 ∷ heightF 18.0 ∷ attr "rx" "2" ∷ attr "ry" "2" ∷ [] ) []
    ∷ line' ( x1_ "16" ∷ y1_ "2" ∷ x2_ "16" ∷ y2_ "6" ∷ [] ) []
    ∷ line' ( x1_ "8" ∷ y1_ "2" ∷ x2_ "8" ∷ y2_ "6" ∷ [] ) []
    ∷ line' ( x1_ "3" ∷ y1_ "10" ∷ x2_ "21" ∷ y2_ "10" ∷ [] ) []
    ∷ [] )

-- | Lock 🔒
iconLock : ∀ {M A} → Float → Node M A
iconLock size =
  icon size size "icon-lock"
    ( rect' ( xF 3.0 ∷ yF 11.0 ∷ widthF 18.0 ∷ heightF 11.0 ∷ attr "rx" "2" ∷ attr "ry" "2" ∷ [] ) []
    ∷ path' ( d_ "M7 11V7a5 5 0 0 1 10 0v4" ∷ [] ) []
    ∷ [] )

-- | Unlock 🔓
iconUnlock : ∀ {M A} → Float → Node M A
iconUnlock size =
  icon size size "icon-unlock"
    ( rect' ( xF 3.0 ∷ yF 11.0 ∷ widthF 18.0 ∷ heightF 11.0 ∷ attr "rx" "2" ∷ attr "ry" "2" ∷ [] ) []
    ∷ path' ( d_ "M7 11V7a5 5 0 0 1 9.9-1" ∷ [] ) []
    ∷ [] )

-- | Eye (visible) 👁️
iconEye : ∀ {M A} → Float → Node M A
iconEye size =
  icon size size "icon-eye"
    ( path' ( d_ "M1 12s4-8 11-8 11 8 11 8-4 8-11 8-11-8-11-8z" ∷ [] ) []
    ∷ circle' ( cxF 12.0 ∷ cyF 12.0 ∷ rF 3.0 ∷ [] ) []
    ∷ [] )

-- | Eye off (hidden) 👁️‍🗨️
iconEyeOff : ∀ {M A} → Float → Node M A
iconEyeOff size =
  icon size size "icon-eye-off"
    ( path' ( d_ "M17.94 17.94A10.07 10.07 0 0 1 12 20c-7 0-11-8-11-8a18.45 18.45 0 0 1 5.06-5.94M9.9 4.24A9.12 9.12 0 0 1 12 4c7 0 11 8 11 8a18.5 18.5 0 0 1-2.16 3.19m-6.72-1.07a3 3 0 1 1-4.24-4.24" ∷ [] ) []
    ∷ line' ( x1_ "1" ∷ y1_ "1" ∷ x2_ "23" ∷ y2_ "23" ∷ [] ) []
    ∷ [] )

-- | Link 🔗
iconLink : ∀ {M A} → Float → Node M A
iconLink size =
  icon size size "icon-link"
    ( path' ( d_ "M10 13a5 5 0 0 0 7.54.54l3-3a5 5 0 0 0-7.07-7.07l-1.72 1.71" ∷ [] ) []
    ∷ path' ( d_ "M14 11a5 5 0 0 0-7.54-.54l-3 3a5 5 0 0 0 7.07 7.07l1.71-1.71" ∷ [] ) []
    ∷ [] )

-- | External link ↗️
iconExternalLink : ∀ {M A} → Float → Node M A
iconExternalLink size =
  icon size size "icon-external-link"
    ( path' ( d_ "M18 13v6a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h6" ∷ [] ) []
    ∷ polyline' ( attr "points" "15 3 21 3 21 9" ∷ [] ) []
    ∷ line' ( x1_ "10" ∷ y1_ "14" ∷ x2_ "21" ∷ y2_ "3" ∷ [] ) []
    ∷ [] )

-- | Share 📤
iconShare : ∀ {M A} → Float → Node M A
iconShare size =
  icon size size "icon-share"
    ( circle' ( cxF 18.0 ∷ cyF 5.0 ∷ rF 3.0 ∷ [] ) []
    ∷ circle' ( cxF 6.0 ∷ cyF 12.0 ∷ rF 3.0 ∷ [] ) []
    ∷ circle' ( cxF 18.0 ∷ cyF 19.0 ∷ rF 3.0 ∷ [] ) []
    ∷ line' ( x1_ "8.59" ∷ y1_ "13.51" ∷ x2_ "15.42" ∷ y2_ "17.49" ∷ [] ) []
    ∷ line' ( x1_ "15.41" ∷ y1_ "6.51" ∷ x2_ "8.59" ∷ y2_ "10.49" ∷ [] ) []
    ∷ [] )

-- | Filter 🔍
iconFilter : ∀ {M A} → Float → Node M A
iconFilter size =
  icon size size "icon-filter"
    ( path' ( d_ "M22 3H2l8 9.46V19l4 2v-8.54L22 3z" ∷ [] ) []
    ∷ [] )

-- | Grid ▦
iconGrid : ∀ {M A} → Float → Node M A
iconGrid size =
  icon size size "icon-grid"
    ( rect' ( xF 3.0 ∷ yF 3.0 ∷ widthF 7.0 ∷ heightF 7.0 ∷ [] ) []
    ∷ rect' ( xF 14.0 ∷ yF 3.0 ∷ widthF 7.0 ∷ heightF 7.0 ∷ [] ) []
    ∷ rect' ( xF 14.0 ∷ yF 14.0 ∷ widthF 7.0 ∷ heightF 7.0 ∷ [] ) []
    ∷ rect' ( xF 3.0 ∷ yF 14.0 ∷ widthF 7.0 ∷ heightF 7.0 ∷ [] ) []
    ∷ [] )

-- | List ☰
iconList : ∀ {M A} → Float → Node M A
iconList size =
  icon size size "icon-list"
    ( line' ( x1_ "8" ∷ y1_ "6" ∷ x2_ "21" ∷ y2_ "6" ∷ [] ) []
    ∷ line' ( x1_ "8" ∷ y1_ "12" ∷ x2_ "21" ∷ y2_ "12" ∷ [] ) []
    ∷ line' ( x1_ "8" ∷ y1_ "18" ∷ x2_ "21" ∷ y2_ "18" ∷ [] ) []
    ∷ line' ( x1_ "3" ∷ y1_ "6" ∷ x2_ "3.01" ∷ y2_ "6" ∷ [] ) []
    ∷ line' ( x1_ "3" ∷ y1_ "12" ∷ x2_ "3.01" ∷ y2_ "12" ∷ [] ) []
    ∷ line' ( x1_ "3" ∷ y1_ "18" ∷ x2_ "3.01" ∷ y2_ "18" ∷ [] ) []
    ∷ [] )

-- | Loader (spinner) ⟳
iconLoader : ∀ {M A} → Float → Node M A
iconLoader size =
  icon size size "icon-loader"
    ( line' ( x1_ "12" ∷ y1_ "2" ∷ x2_ "12" ∷ y2_ "6" ∷ [] ) []
    ∷ line' ( x1_ "12" ∷ y1_ "18" ∷ x2_ "12" ∷ y2_ "22" ∷ [] ) []
    ∷ line' ( x1_ "4.93" ∷ y1_ "4.93" ∷ x2_ "7.76" ∷ y2_ "7.76" ∷ [] ) []
    ∷ line' ( x1_ "16.24" ∷ y1_ "16.24" ∷ x2_ "19.07" ∷ y2_ "19.07" ∷ [] ) []
    ∷ line' ( x1_ "2" ∷ y1_ "12" ∷ x2_ "6" ∷ y2_ "12" ∷ [] ) []
    ∷ line' ( x1_ "18" ∷ y1_ "12" ∷ x2_ "22" ∷ y2_ "12" ∷ [] ) []
    ∷ line' ( x1_ "4.93" ∷ y1_ "19.07" ∷ x2_ "7.76" ∷ y2_ "16.24" ∷ [] ) []
    ∷ line' ( x1_ "16.24" ∷ y1_ "7.76" ∷ x2_ "19.07" ∷ y2_ "4.93" ∷ [] ) []
    ∷ [] )

-- | Maximize ⤢
iconMaximize : ∀ {M A} → Float → Node M A
iconMaximize size =
  icon size size "icon-maximize"
    ( path' ( d_ "M8 3H5a2 2 0 0 0-2 2v3m18 0V5a2 2 0 0 0-2-2h-3m0 18h3a2 2 0 0 0 2-2v-3M3 16v3a2 2 0 0 0 2 2h3" ∷ [] ) []
    ∷ [] )

-- | Minimize ⤡
iconMinimize : ∀ {M A} → Float → Node M A
iconMinimize size =
  icon size size "icon-minimize"
    ( path' ( d_ "M4 14h6v6M20 10h-6V4M14 10l7-7M3 21l7-7" ∷ [] ) []
    ∷ [] )

-- | Zap (lightning) ⚡
iconZap : ∀ {M A} → Float → Node M A
iconZap size =
  icon size size "icon-zap"
    ( path' ( d_ "M13 2L3 14h9l-1 8 10-12h-9l1-8z" ∷ fill_ "currentColor" ∷ [] ) []
    ∷ [] )

-- | Globe 🌐
iconGlobe : ∀ {M A} → Float → Node M A
iconGlobe size =
  icon size size "icon-globe"
    ( circle' ( cxF 12.0 ∷ cyF 12.0 ∷ rF 10.0 ∷ [] ) []
    ∷ line' ( x1_ "2" ∷ y1_ "12" ∷ x2_ "22" ∷ y2_ "12" ∷ [] ) []
    ∷ path' ( d_ "M12 2a15.3 15.3 0 0 1 4 10 15.3 15.3 0 0 1-4 10 15.3 15.3 0 0 1-4-10 15.3 15.3 0 0 1 4-10z" ∷ [] ) []
    ∷ [] )

