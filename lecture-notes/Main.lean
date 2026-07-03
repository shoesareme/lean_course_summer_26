import VersoSlides
import Lecture1

open VersoSlides

-- Embedded so the generated deck remains self-contained and works offline.
def lectureTheme : CssFile where
  filename := "lecture-theme.css"
  contents := ⟨include_str "theme.css"⟩

def main : IO UInt32 :=
  slidesMain
    (config := {
      theme := "white"
      transition := "fade"
      width := 1280
      height := 720
      margin := 0.06
      controls := true
      progress := true
      slideNumber := true
      hash := true
      center := true
      extraCss := #[lectureTheme]
      outputDir := "lecture-notes/output/lecture-01"
    })
    (doc := %doc Lecture1)
