prelude
import Init.Prelude
namespace StringLiteralProbe
theorem empty : Eq "" (String.ofList (@List.nil Char)) := Eq.refl ""
theorem ascii : Eq "A" (String.ofList (@List.cons Char 'A' (@List.nil Char))) := Eq.refl "A"
theorem unicode : Eq "é🦀" (String.ofList (@List.cons Char 'é' (@List.cons Char '🦀' (@List.nil Char)))) := Eq.refl "é🦀"
theorem nul : Eq "\x00" (String.ofList (@List.cons Char '\x00' (@List.nil Char))) := Eq.refl "\x00"
theorem balanced : Eq "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" := Eq.refl "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
end StringLiteralProbe
