{-# OPTIONS --without-K #-}

-- Html Elements: all HTML elements

module Agdelte.Html.Elements where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)

open import Agdelte.Html.Types

private
  variable
    Msg : Set

------------------------------------------------------------------------
-- Document structure
------------------------------------------------------------------------

div : List (Attr Msg) → List (Html Msg) → Html Msg
div = node "div"

span : List (Attr Msg) → List (Html Msg) → Html Msg
span = node "span"

section : List (Attr Msg) → List (Html Msg) → Html Msg
section = node "section"

article : List (Attr Msg) → List (Html Msg) → Html Msg
article = node "article"

aside : List (Attr Msg) → List (Html Msg) → Html Msg
aside = node "aside"

header : List (Attr Msg) → List (Html Msg) → Html Msg
header = node "header"

footer : List (Attr Msg) → List (Html Msg) → Html Msg
footer = node "footer"

main' : List (Attr Msg) → List (Html Msg) → Html Msg
main' = node "main"

nav : List (Attr Msg) → List (Html Msg) → Html Msg
nav = node "nav"

------------------------------------------------------------------------
-- Headings
------------------------------------------------------------------------

h1 : List (Attr Msg) → List (Html Msg) → Html Msg
h1 = node "h1"

h2 : List (Attr Msg) → List (Html Msg) → Html Msg
h2 = node "h2"

h3 : List (Attr Msg) → List (Html Msg) → Html Msg
h3 = node "h3"

h4 : List (Attr Msg) → List (Html Msg) → Html Msg
h4 = node "h4"

h5 : List (Attr Msg) → List (Html Msg) → Html Msg
h5 = node "h5"

h6 : List (Attr Msg) → List (Html Msg) → Html Msg
h6 = node "h6"

------------------------------------------------------------------------
-- Text content
------------------------------------------------------------------------

p : List (Attr Msg) → List (Html Msg) → Html Msg
p = node "p"

pre : List (Attr Msg) → List (Html Msg) → Html Msg
pre = node "pre"

code : List (Attr Msg) → List (Html Msg) → Html Msg
code = node "code"

blockquote : List (Attr Msg) → List (Html Msg) → Html Msg
blockquote = node "blockquote"

hr : List (Attr Msg) → Html Msg
hr attrs = node "hr" attrs []

br : List (Attr Msg) → Html Msg
br attrs = node "br" attrs []

------------------------------------------------------------------------
-- Inline text
------------------------------------------------------------------------

a : List (Attr Msg) → List (Html Msg) → Html Msg
a = node "a"

strong : List (Attr Msg) → List (Html Msg) → Html Msg
strong = node "strong"

em : List (Attr Msg) → List (Html Msg) → Html Msg
em = node "em"

b : List (Attr Msg) → List (Html Msg) → Html Msg
b = node "b"

i : List (Attr Msg) → List (Html Msg) → Html Msg
i = node "i"

u : List (Attr Msg) → List (Html Msg) → Html Msg
u = node "u"

s : List (Attr Msg) → List (Html Msg) → Html Msg
s = node "s"

small : List (Attr Msg) → List (Html Msg) → Html Msg
small = node "small"

sub : List (Attr Msg) → List (Html Msg) → Html Msg
sub = node "sub"

sup : List (Attr Msg) → List (Html Msg) → Html Msg
sup = node "sup"

mark : List (Attr Msg) → List (Html Msg) → Html Msg
mark = node "mark"

------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

ul : List (Attr Msg) → List (Html Msg) → Html Msg
ul = node "ul"

ol : List (Attr Msg) → List (Html Msg) → Html Msg
ol = node "ol"

li : List (Attr Msg) → List (Html Msg) → Html Msg
li = node "li"

dl : List (Attr Msg) → List (Html Msg) → Html Msg
dl = node "dl"

dt : List (Attr Msg) → List (Html Msg) → Html Msg
dt = node "dt"

dd : List (Attr Msg) → List (Html Msg) → Html Msg
dd = node "dd"

------------------------------------------------------------------------
-- Forms
------------------------------------------------------------------------

form : List (Attr Msg) → List (Html Msg) → Html Msg
form = node "form"

input : List (Attr Msg) → Html Msg
input attrs = node "input" attrs []

textarea : List (Attr Msg) → List (Html Msg) → Html Msg
textarea = node "textarea"

button : List (Attr Msg) → List (Html Msg) → Html Msg
button = node "button"

select : List (Attr Msg) → List (Html Msg) → Html Msg
select = node "select"

option : List (Attr Msg) → List (Html Msg) → Html Msg
option = node "option"

optgroup : List (Attr Msg) → List (Html Msg) → Html Msg
optgroup = node "optgroup"

label : List (Attr Msg) → List (Html Msg) → Html Msg
label = node "label"

fieldset : List (Attr Msg) → List (Html Msg) → Html Msg
fieldset = node "fieldset"

legend : List (Attr Msg) → List (Html Msg) → Html Msg
legend = node "legend"

------------------------------------------------------------------------
-- Tables
------------------------------------------------------------------------

table : List (Attr Msg) → List (Html Msg) → Html Msg
table = node "table"

thead : List (Attr Msg) → List (Html Msg) → Html Msg
thead = node "thead"

tbody : List (Attr Msg) → List (Html Msg) → Html Msg
tbody = node "tbody"

tfoot : List (Attr Msg) → List (Html Msg) → Html Msg
tfoot = node "tfoot"

tr : List (Attr Msg) → List (Html Msg) → Html Msg
tr = node "tr"

th : List (Attr Msg) → List (Html Msg) → Html Msg
th = node "th"

td : List (Attr Msg) → List (Html Msg) → Html Msg
td = node "td"

caption : List (Attr Msg) → List (Html Msg) → Html Msg
caption = node "caption"

------------------------------------------------------------------------
-- Media
------------------------------------------------------------------------

img : List (Attr Msg) → Html Msg
img attrs = node "img" attrs []

audio : List (Attr Msg) → List (Html Msg) → Html Msg
audio = node "audio"

video : List (Attr Msg) → List (Html Msg) → Html Msg
video = node "video"

source : List (Attr Msg) → Html Msg
source attrs = node "source" attrs []

canvas : List (Attr Msg) → List (Html Msg) → Html Msg
canvas = node "canvas"

svg : List (Attr Msg) → List (Html Msg) → Html Msg
svg = node "svg"

------------------------------------------------------------------------
-- Interactive
------------------------------------------------------------------------

details : List (Attr Msg) → List (Html Msg) → Html Msg
details = node "details"

summary : List (Attr Msg) → List (Html Msg) → Html Msg
summary = node "summary"

dialog : List (Attr Msg) → List (Html Msg) → Html Msg
dialog = node "dialog"

progress : List (Attr Msg) → List (Html Msg) → Html Msg
progress = node "progress"

meter : List (Attr Msg) → List (Html Msg) → Html Msg
meter = node "meter"

------------------------------------------------------------------------
-- Semantic
------------------------------------------------------------------------

time : List (Attr Msg) → List (Html Msg) → Html Msg
time = node "time"

address : List (Attr Msg) → List (Html Msg) → Html Msg
address = node "address"

figure : List (Attr Msg) → List (Html Msg) → Html Msg
figure = node "figure"

figcaption : List (Attr Msg) → List (Html Msg) → Html Msg
figcaption = node "figcaption"

------------------------------------------------------------------------
-- Convenience shortcuts
------------------------------------------------------------------------

-- Text node
txt : String → Html Msg
txt = text

-- div with text
divText : String → Html Msg
divText s = div [] (text s ∷ [])

-- span with text
spanText : String → Html Msg
spanText s = span [] (text s ∷ [])

-- Button with text
buttonText : List (Attr Msg) → String → Html Msg
buttonText attrs s = button attrs (text s ∷ [])

-- Link with text
aText : List (Attr Msg) → String → Html Msg
aText attrs s = a attrs (text s ∷ [])
